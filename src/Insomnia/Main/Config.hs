module Insomnia.Main.Config where

import qualified System.IO as IO

data InsomniaMainConfig = InsomniaMainConfig {
  ismCfgDebugOut :: IO.Handle -- ^ handle to use for debug output
  , ismCfgErrorOut :: IO.Handle -- ^ handle to use for error output
  , ismCfgFinalProductOut :: Maybe IO.Handle -- ^ where to save the last produced result.
  , ismCfgEvaluateFOmega :: Bool -- ^ if True, run the FOmega code, ow just typecheck it.
  }

defaultConfig :: InsomniaMainConfig
defaultConfig = InsomniaMainConfig {
  ismCfgDebugOut = IO.stdout
  , ismCfgErrorOut = IO.stderr
  , ismCfgFinalProductOut = Nothing
  , ismCfgEvaluateFOmega = True
  }

