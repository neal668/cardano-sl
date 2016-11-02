module Bench.Pos.Remote.Launcher
       ( startSupporter
       , startFullNode
       , startCollector
       , NodeNumber
       ) where

import           Control.Concurrent.Chan  (Chan)
import qualified Control.Concurrent.Chan  as C
import           Control.TimeWarp.Logging (LoggerName (..), Severity (..))
import           Data.Default             (def)
import           Data.List                ((!!))
import qualified Data.Map.Strict          as M
import           Data.Maybe               (fromJust)
import           Formatting               (int, sformat, stext, (%))
import           Text.Parsec              (parse)
import           Universum

import           Pos.CLI                  (addrParser, dhtKeyParser, dhtNodeParser)
import           Pos.Communication        (RequestStat (..), ResponseStat (..))
import           Pos.Crypto               (unsafeHash)
import           Pos.DHT                  (DHTNodeType (..), ListenerDHT (..),
                                           dhtNodeType, sendToNode)
import           Pos.Genesis              (genesisAddresses, genesisSecretKeys,
                                           genesisVssKeyPairs)
import           Pos.Launcher             (BaseParams (..), LoggingParams (..),
                                           NodeParams (..), getCurTimestamp, runNodeStats,
                                           runServiceMode, runSupporterReal,
                                           runTimeLordReal, runTimeSlaveReal)
import           Pos.Statistics           (StatEntry)
import           Pos.Types                (TxOut (..), Utxo)

import           Bench.Pos.Remote.Config  (CollectorConfig (..), FullNodeConfig (..),
                                           SupporterConfig (..), readRemoteConfig)

type NodeNumber = Int

-- | For every static stakeholder it generates `k` coins, but in `k`
-- transaction (1 coin each), where `k` is input parameter.
utxoPetty :: Int -> Utxo
utxoPetty k =
    M.fromList $ flip concatMap genesisAddresses $ \a ->
        map (\i -> ((unsafeHash (show a ++ show i), 0), TxOut a 1)) [1..k]

-- TODO: move to some util library (e. g. `serokell-core`)
eitherPanic :: Show a => Text -> Either a b -> b
eitherPanic msgPrefix = either (panic . (msgPrefix <>) . show) identity

benchLogging :: LoggingParams
benchLogging = def
    { lpMainSeverity = Debug
    , lpDhtSeverity = Just Info
    }

startSupporter :: FilePath -> IO ()
startSupporter config = do
    SupporterConfig {..} <- readRemoteConfig config

    let dhtKey = eitherPanic "Invalid DHT key: " $ parse dhtKeyParser "" $ toString scDhtKey
        keyType = dhtNodeType dhtKey

    when (keyType /= Just DHTSupporter) $
        panic $ sformat ("Invalid type of DHT key: "%stext%" (should be `Just DHTSupporter`)") $ show keyType

    let logging = benchLogging
                  { lpRootLogger = "supporter"
                  }
        params = BaseParams
                 { bpLogging = logging
                 , bpPort = scPort
                 , bpDHTPeers = []
                 , bpDHTKeyOrType = Left dhtKey
                 }

    runSupporterReal params

startFullNode :: FilePath -> NodeNumber -> Bool -> IO ()
startFullNode config nodeNumber isTimeLord = do
    when (nodeNumber >= length genesisAddresses || nodeNumber < 0) $
        panic $ sformat ("Invalid node number "%int%" (should be in range [0.."%int%"])") nodeNumber $
        length genesisAddresses - 1

    FullNodeConfig {..} <- readRemoteConfig config

    let dhtSupporter = eitherPanic "Invalid supporter address: " $ parse dhtNodeParser "" $ toString fncSupporterAddr
        logging = benchLogging
                  { lpRootLogger = LoggerName ("fullnode." ++ show nodeNumber)
                  }
        baseParams =
            BaseParams
            { bpLogging      = logging
            , bpPort         = fncPort
            , bpDHTPeers     = [dhtSupporter]
            , bpDHTKeyOrType = Right DHTFull
            }
        -- TODO: refactor =\
        getSystemStart = if isTimeLord
                         then runTimeLordReal (benchLogging { lpRootLogger = "time-lord" })
                         else runTimeSlaveReal (baseParams { bpLogging = benchLogging { lpRootLogger = "time-slave" } })

    startTime <- getSystemStart
    let params =
            NodeParams
            { npDbPath       = fncDbPath
            -- always start with a fresh database (maybe will change later)
            , npRebuildDb    = True
            , npSystemStart  = startTime
            , npSecretKey    = genesisSecretKeys !! nodeNumber
            , npVssKeyPair   = genesisVssKeyPairs !! nodeNumber
            , npBaseParams   = baseParams
            , npCustomUtxo   = Just $ utxoPetty 10000
            }

    runNodeStats params

collectorListener :: MonadIO m => Chan (ResponseStat StatEntry) -> ResponseStat StatEntry -> m ()
collectorListener channel res = liftIO $ writeChan channel res

startCollector :: FilePath -> IO ()
startCollector config = do
    CollectorConfig {..} <- readRemoteConfig config

    let addrs = eitherPanic "Invalid address: " $ mapM (parse addrParser "" . toString) ccNodes
        enumAddrs = zip [0..] addrs
        params =
            BaseParams
            { bpLogging = def
            , bpPort = 8095
            , bpDHTPeers = []
            , bpDHTKeyOrType = Right DHTClient
            }

    ch <- C.newChan
    runServiceMode params [ListenerDHT $ collectorListener ch] $ do
        forM_ enumAddrs $ \(idx, addr) -> do
            sendToNode addr (RequestStat idx "received_transaction")
            sendToNode addr (RequestStat idx "sent_transaction")
            sendToNode addr (RequestStat idx "received_block_header")
            sendToNode addr (RequestStat idx "sent_block_header")
            sendToNode addr (RequestStat idx "received_block_body")
            sendToNode addr (RequestStat idx "sent_block_body")

        forM_ [0 .. 6 * length addrs] $ \_ -> liftIO $ do
           (ResponseStat id label res) <- readChan ch
           print id
           print label
           print res
