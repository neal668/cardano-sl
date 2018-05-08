{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE ViewPatterns               #-}

module UTxO.BlockGen
    ( genValidBlocktree
    , divvyUp
    , estimateFee
    ) where

import           Universum hiding (use, (%~), (.~), (^.))

import           Control.Category (id)
import           Control.Exception (throw)
import           Control.Lens hiding (elements)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set
import           Data.Tree (Tree)
import qualified Data.Tree as Tree
import           GHC.Stack (HasCallStack)
import           Pos.Util.Chrono
import           System.IO.Error (userError)
import           Test.QuickCheck hiding (elements)
import qualified Test.QuickCheck as QuickCheck

import           Util.DepIndep
import           UTxO.Context
import           UTxO.DSL
import           UTxO.PreChain

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

-- | Variation on 'replicateM' with state and potential early termination
replicateSt :: Monad m => Int -> (s -> m (Maybe (a, s))) -> (s -> m ([a], s))
replicateSt 0 _ st = return ([], st)
replicateSt n f st = do
    ma <- f st
    case ma of
      Nothing       -> return ([], st)
      Just (a, st') -> do (as, st'') <- replicateSt (n - 1) f st'
                          return (a : as, st'')

-- | Variation on QuickCheck's elements with a better callstack on errors
elements :: HasCallStack => [a] -> Gen a
elements [] = throw $ userError ("elements: empty list at " ++ prettyCallStack callStack)
elements xs = QuickCheck.elements xs

-- | Choose (up to) @n@ /distinct/ elements out of the given list
distinct :: Int -> [a] -> Gen [a]
distinct 0 _  = return []
distinct _ [] = return []
distinct n xs = do
    i <- choose (0, length xs - 1)
    let (xsBefore, x:xsAfter) = splitAt i xs
    (x:) <$> distinct (n - 1) (xsBefore ++ xsAfter)

{-------------------------------------------------------------------------------
  Preliminaries
-------------------------------------------------------------------------------}

selectSomeInputs' :: Hash h Addr
                  => Int
                  -> Utxo h Addr
                  -> Gen (NonEmpty (Input h Addr, Output Addr))
selectSomeInputs' upperLimit (utxoToMap -> utxoMap) = do
    input1 <- elements (Map.toList utxoMap)
    -- it seems likely that we'll want to weight the frequency of
    -- just-one-input more heavily than lots-of-inputs
    n <- frequency $ zip
            [upperLimit, upperLimit-1 .. 0]
            (map pure [0 .. upperLimit])
    otherInputs <- loop (Map.delete (fst input1) utxoMap) n
    pure (input1 :| otherInputs)
  where
    loop utxo n
        | n <= 0 || Map.null utxo = pure []
        | otherwise = do
            inp <- elements (Map.toList utxo)
            rest <- loop (Map.delete (fst inp) utxo) (n - 1)
            pure (inp : rest)

-- | Given a set of inputs, tagged with their output values, and a set of output
-- addresses, construct a transaction by dividing the sum total of the inputs
-- evenly over the output addresses.
divvyUp
    :: (HasCallStack, Hash h Addr)
    => Int -- ^ hash
    -> NonEmpty (Input h Addr, Output Addr)
    -> NonEmpty Addr
    -> Value
    -> Transaction h Addr
divvyUp h inputs'outputs destinations fee = tx
  where
    tx = Transaction {
             trFresh = 0
           , trFee   = fee
           , trHash  = h
           , trIns   = inputs
           , trOuts  = outputs
           , trExtra = []
           }
    inputs = foldMap (Set.singleton . fst) inputs'outputs
    destLen = fromIntegral (length destinations)
    -- if we don't know what the fee is yet (eg a 0), then we want to use
    -- the max fee for safety's sake
    totalValue = sum (map (outVal . snd) inputs'outputs)
        `safeSubtract` if fee == 0 then estimateFee tx else fee
    valPerOutput = totalValue `div` destLen
    outputs = toList (map (\addr -> Output addr valPerOutput) destinations)

-- | 'Value' is an alias for 'Word64', which underflows. This detects
-- underflow and returns @0@ for underflowing values.
safeSubtract :: Value -> Value -> Value
safeSubtract x y
    | z > x     = 0
    | otherwise = z
  where
    z = x - y

-- | Conversatively estimate the fee for this transaction
--
-- Result may be larger than the minimum fee, but not smaller.
-- TODO: Right now this does not take the transaction structure into account.
-- We should come up with a more precise model here.
estimateFee :: Transaction h a -> Value
estimateFee _ = maxFee
  where
    maxFee = 280000

withEstimatedFee :: (Value -> Transaction h a) -> Transaction h a
withEstimatedFee tx = let tx0 = tx 0 in tx0 { trFee = estimateFee tx0 }

{-------------------------------------------------------------------------------
  Forkable blockchains
-------------------------------------------------------------------------------}

type NoFeeBlockTree h = Tree [Value -> Transaction h Addr]

-- | Global context for building block trees.
--   This structure is shared between all branches, and controls the
--   extent to which the tree forks.
data TreeGenGlobalCtx h = TreeGenGlobalCtx
    { _treeGenGlobalCtxFreshHashSrc                :: !Int
      -- ^ A fresh hash value for each new transaction.
    {- The below values form part of configuration, and are unlikely to be
       updated during tree building.
    -}
    , _treeGenGlobalCtxAddresses                   :: ![Addr]
      -- ^ The addresses we can choose from when generating transaction outputs
    , _treeGenGlobalCtxInputPartiesUpperLimit      :: !Int
      -- ^ The upper limit on the number of parties that may be selected as
      -- inputs to a transaction.
    , _treeGenGlobalCtxOutputPartiesUpperLimit     :: !Int
      -- ^ The upper limit on the number of parties that may be selected as
      -- outputs to a transaction.
    , _treeGenGlobalCtxForkLikelihood              :: !Double
      -- ^ Likelihood of generating a forked block at any point in the tree.
      --   Only the non-integer part of this value is considered.
    , _treeGenGlobalCtxPruneLikelihood             :: !Double
      -- ^ Likelihood of the non-principal branch to be terminated at any
      --   block.
    , _treeGenGlobalCtxMaxHeight                   :: !Int
      -- ^ Maximum height of the tree. The principal branch will be grown to
      --   this height. In order to preserve the property that we only switch
      --   to longer forks, if any other branch grows to this height, it will
      --   be terminated at (maxHeight - 1).
    , _treeGenGlobalCtxSharedTransactionLikelihood :: !Double
      -- ^ The likelihood that a given transaction will be shared between two
      --   blocks with the same parent.
    , _treeGenGlobalCtxBootTransaction             :: Transaction h Addr
      -- ^ Boot transaction
    }

data TreeGenBranchCtx h = TreeGenBranchCtx
    { _treeGenBranchCtxPrincipalBranch :: !Bool
      -- ^ Is this the principal branch? The principal branch will never
      --   be pruned.
    , _treeGenBranchCtxBranchHeight    :: !Int
      -- ^ Height of the tip of the branch (from the root).
    , _treeGenBranchCtxCurrentUtxo     :: !(Utxo h Addr)
      -- ^ The mapping of current addresses and their current account values.
    , _treeGenBranchCtxTransactions    :: ![Value -> Transaction h Addr]
      -- ^ Transactions to form this block. This is stored here because we
      --   generate all transactions for the child block at the parent level,
      --   in order to facilitate sharing.
    }

makeFields ''TreeGenGlobalCtx
makeFields ''TreeGenBranchCtx

-- | Provide a fresh hash value for a transaction.
freshHash :: ( HasFreshHashSrc src Int
             , MonadState src m
             )
          => m Int
freshHash = do
    i <- use freshHashSrc
    freshHashSrc += 1
    pure i

nonAvvmUtxo :: HasCurrentUtxo src (Utxo h Addr)
            => Getter src (Utxo h Addr)
nonAvvmUtxo =
    currentUtxo . to (utxoRestrictToAddr (not . isAvvmAddr))


initTreeGenGlobalCtx :: Transaction h Addr -> TreeGenGlobalCtx h
initTreeGenGlobalCtx boot = TreeGenGlobalCtx
    { _treeGenGlobalCtxFreshHashSrc                = 1
    , _treeGenGlobalCtxAddresses                   = addrs
    , _treeGenGlobalCtxInputPartiesUpperLimit      = 2
    , _treeGenGlobalCtxOutputPartiesUpperLimit     = 3
    , _treeGenGlobalCtxForkLikelihood              = 0.1
    , _treeGenGlobalCtxPruneLikelihood             = 0.3
    , _treeGenGlobalCtxMaxHeight                   = 50
    , _treeGenGlobalCtxSharedTransactionLikelihood = 0.5
    , _treeGenGlobalCtxBootTransaction             = boot
    }
  where
    -- Output addresses
    --
    -- TODO: we may want to make this set larger
    -- (i.e. generate additional addresses for the poor actors)
    addrs = filter (not . isAvvmAddr) . map outAddr $ trOuts boot

-- | Tree generation monad.
newtype TreeGen h a = TreeGen
    { unTreeGen :: StateT (TreeGenGlobalCtx h) Gen a
    } deriving (Functor, Applicative, Monad, MonadState (TreeGenGlobalCtx h))

-- | Lift a 'Gen' action into the 'TreeGen' monad.
liftGenTree :: Gen a -> TreeGen h a
liftGenTree = TreeGen . lift

genValidBlocktree :: Hash h Addr => PreTree h Gen ()
genValidBlocktree = toPreTreeWith identity newTree

selectDestination :: TreeGen h Addr
selectDestination = (liftGenTree . elements) =<< use addresses

toPreTreeWith
    :: Hash h Addr
    => (TreeGenGlobalCtx h -> TreeGenGlobalCtx h) -- ^ Modify the global settings
    -> TreeGen h (NoFeeBlockTree h)
    -> PreTree h Gen ()
toPreTreeWith settings bg = DepIndep $ \(boot :: Transaction h Addr)-> do
    ks <- evalStateT (unTreeGen bg) (settings (initTreeGenGlobalCtx boot))
    return $ \fees -> (markOldestFirst (zipTreeFees ks fees), ())
  where
    markOldestFirst = OldestFirst . fmap OldestFirst


newTree :: forall h. Hash h Addr
        => TreeGen h (NoFeeBlockTree h)
newTree = do
    boot <- use bootTransaction
    -- Choose a random height for the blocktree
    height <- liftGenTree $ choose (10, 50)
    maxHeight .= height
    Tree.unfoldTreeM buildTree $ initBranchCtx boot
  where
    initBranchCtx boot = TreeGenBranchCtx True 0 (trUtxo boot) []
    buildTree :: TreeGenBranchCtx h
              -> TreeGen h ([Value -> Transaction h Addr], [TreeGenBranchCtx h])
    buildTree branchCtx = do
      let curHeight = branchCtx ^. branchHeight

      -- Firstly, decide whether we should prune this branch. We prune if
      -- - we have reached the maximum height, or
      -- - we are not the principal branch, and
      -- - - we have reached the maximum height - 1, or
      -- - - with probability equal to the prune likelihood
      toPrune <- do
        pl <- use pruneLikelihood
        maxH <- use maxHeight
        toss <- liftGenTree $ choose (0,1)
        return $ (curHeight >= maxH)
               || ((not $ branchCtx ^. principalBranch)
                   && ((curHeight >= maxH - 1) || toss < pl)
                  )

      if toPrune
      then return (branchCtx ^. transactions, [])
      else do
        -- At each 'level', we first work out how many branches to generate. We
        -- then generate a number of transactions T and select from the set of
        -- transactions (with replacement). This should result in a relatively
        -- high degree of transactions shared between branches.
        numBranches <- case curHeight of
          0 -> pure 1  -- we don't branch on the first block.
          _ -> liftGenTree . branchCount =<< use forkLikelihood
        branchSizes <- liftGenTree $ vectorOf numBranches $ choose (1, 10)
        stl <- use sharedTransactionLikelihood
        (txs, _) <- replicateSt
          (ceiling $ fromIntegral (maximum branchSizes) / stl)
          generateTransaction
          (branchCtx ^. nonAvvmUtxo)

        -- One may ask why we set the 'last' branch as principal. This is to
        -- reduce the amount of state being carried during constructing. The
        -- principal branch is expected to be the longest, so we would like to
        -- finish constructing short forks early.
        branches <- forM (zip [0..] branchSizes) $ \(idx, bs) -> do
          mytxs <- liftGenTree $ distinct bs txs
          return $ branchCtx
            & (branchHeight    +~ 1)
            . (principalBranch .~ (idx == numBranches -1))
            . (transactions    .~ mytxs)
            . (currentUtxo      %~ (foldr (.) id $ utxoApply . withEstimatedFee <$> mytxs))

        return (branchCtx ^. transactions, branches)

    -- Calculate the number of branches to generate. We keep tossing a
    -- 'p'-weighted coin until we get a tails.
    branchCount :: Double -> Gen Int
    branchCount p = go 1 where
      go count = do
        toss <- choose (0,1)
        if toss > p then return count else go $ count + 1

    generateTransaction :: Utxo h Addr
                        -> TreeGen h (Maybe (Value -> Transaction h Addr, Utxo h Addr))
    generateTransaction utxo = do
      if utxoNull utxo then
        return Nothing
      else do
        hash'          <- freshHash
        maxNumInputs   <- use inputPartiesUpperLimit
        maxNumOutputs  <- use outputPartiesUpperLimit
        inputs'outputs <- liftGenTree $ selectSomeInputs' maxNumInputs utxo
        numOutputs     <- liftGenTree $ choose (1, maxNumOutputs)
        destinations   <- NE.fromList <$> replicateM numOutputs selectDestination
        -- TODO: Right now this generates blocks with no dependent transactions
        -- in them. We could relax that restriction, but if we do then the code
        -- above needs to be modified also: we can no longer pick a random subset
        -- of these transactions and assume that they are valid together.
        let inputs = Set.fromList $ toList (fmap fst inputs'outputs)
            utxo'  = utxoRemoveInputs inputs utxo
        return $ Just (divvyUp hash' inputs'outputs destinations, utxo')

zipTreeFees
    :: Tree [Value -> Transaction h Addr]
    -> (Tree [Value] -> Tree [Transaction h Addr])
zipTreeFees = curry $ Tree.unfoldTree go
  where
    go (Tree.Node f txChildren, Tree.Node fee feeChildren) =
      (zipWith ($) f fee, zip txChildren feeChildren)
