module Insomnia.Main.Monad where

import Control.Monad.Reader
import Data.Monoid ((<>))

import System.Exit (exitFailure)
import qualified System.IO as IO

import qualified Data.Format as F

import Insomnia.Main.Config

type InsomniaMain = ReaderT InsomniaMainConfig IO

runInsomniaMain :: InsomniaMain a -> InsomniaMainConfig -> IO a
runInsomniaMain = runReaderT 

putErrorStrLn :: String -> InsomniaMain ()
putErrorStrLn msg =
 asks ismCfgErrorOut >>= \h -> lift $ IO.hPutStrLn h msg

putDebugStrLn :: String -> InsomniaMain ()
putDebugStrLn msg =
 asks ismCfgDebugOut >>= \h -> lift $ IO.hPutStrLn h msg

putErrorDoc :: F.Doc -> InsomniaMain ()
putErrorDoc d = asks ismCfgErrorOut >>= \h -> lift $ F.hPutStrDoc h d

putDebugDoc :: F.Doc -> InsomniaMain ()
putDebugDoc d = asks ismCfgDebugOut >>= \h -> lift $ F.hPutStrDoc h d

showErrorAndDie :: (F.Format err) => String -> err -> InsomniaMain a
showErrorAndDie phase msg = do
  putErrorStrLn $ "Encountered error while " ++ phase
  putErrorDoc (F.format msg <> F.newline)
  lift $ exitFailure
