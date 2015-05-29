{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main (
  -- * Nice entry points
  interpreterMain, compilerMain
  -- * Lower level entry point
  , Command(..)
  , commandMain
  -- * Plumbing
  , InsomniaMain
  , runInsomniaMain
  , parseAndCheck
  , InsomniaMainConfig(..)
  , defaultConfig
  ) where

import qualified System.IO as IO
import qualified System.FilePath as FP

import Insomnia.Main.Monad (InsomniaMain, runInsomniaMain)
import Insomnia.Main.Config (InsomniaMainConfig(..), defaultConfig)
import Insomnia.Main.Command (Command(..), processArguments, printUsage)
import Insomnia.Main.InsomniaStages (parseAndCheck, parseAndCheckAndGamble)

interpreterMain :: IO ()
interpreterMain = do
  act <- processArguments
  commandMain act

commandMain :: Command -> IO ()
commandMain act =
  case act of
    Typecheck fp -> runInsomniaMain (parseAndCheck fp) defaultConfig
    Gamble fp -> do
      let fpOut = FP.addExtension (FP.dropExtension fp ) ".rkt"
      IO.withFile fpOut IO.WriteMode $ \hOut -> do
        let config = defaultConfig { ismCfgEvaluateFOmega = False
                                   , ismCfgFinalProductOut = Just hOut
                                   }
        runInsomniaMain (parseAndCheckAndGamble fp) config
    HelpUsage -> printUsage

compilerMain :: IO ()
compilerMain = do
  act_ <- processArguments
  let act = case act_ of
        Typecheck fp -> Gamble fp
        _ -> act_
  commandMain act

