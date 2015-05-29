module Insomnia.Main.Config where

import qualified System.IO as IO

data InsomniaMainConfig = InsomniaMainConfig {
  ismCfgDebugOut :: IO.Handle -- ^ handle to use for debug output
  , ismCfgErrorOut :: IO.Handle -- ^ handle to use for error output
  , ismCfgEvaluateFOmega :: Bool -- ^ if True, run the FOmega code, ow just typecheck it.
  }

defaultConfig :: InsomniaMainConfig
defaultConfig = InsomniaMainConfig {
  ismCfgDebugOut = IO.stdout
  , ismCfgErrorOut = IO.stderr
  , ismCfgEvaluateFOmega = True
  }

