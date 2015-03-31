{-# LANGUAGE DeriveDataTypeable #-}
module InsomniaProvider (testInsomnia) where

import qualified Control.Exception as Exn

import Data.Typeable (Typeable)
import Data.Tagged (Tagged(..))

import qualified System.IO as IO
import qualified System.IO.Temp as IOTemp
import qualified System.Exit as ExitCode

import qualified Insomnia.Main as Insomnia

import Test.Tasty (TestTree, TestName)
import Test.Tasty.Providers (IsTest(..), singleTest, testPassed, testFailed)

import InsomniaFlagScraper (scrapeFlags, ScrapedFlags(..))

newtype InsomniaTest = InsomniaTest { insomniaTestFilePath :: FilePath }
                       deriving (Show, Typeable)

instance IsTest InsomniaTest where
  run _opts (InsomniaTest fp) _reportProgress = do
    IOTemp.withTempFile "dist/test" "ism." $ \logFP logHandle -> do
      let succeeded = testPassed ""
      (ScrapedFlags evalFOmega) <- scrapeFlags' fp
      (runInsomnia logHandle evalFOmega fp >> return succeeded)
        `Exn.catch` (\e ->
                    case e of
                     ExitCode.ExitSuccess -> return succeeded
                     ExitCode.ExitFailure _ -> do
                       IO.hClose logHandle
                       log <- IO.readFile logFP
                       return $ testFailed $ log)

  testOptions = Tagged []

runInsomnia :: IO.Handle -> Bool -> FilePath -> IO ()
runInsomnia logHandle evalFOmega fp =  do
  Insomnia.runInsomniaMain (Insomnia.parseAndCheck fp)
  $ Insomnia.defaultConfig {
    Insomnia.ismCfgDebugOut = logHandle
    , Insomnia.ismCfgErrorOut = logHandle
    , Insomnia.ismCfgEvaluateFOmega = evalFOmega -- TODO: make this configurable on a per-test basis
    }

testInsomnia :: TestName -> FilePath -> TestTree
testInsomnia name = singleTest name . InsomniaTest
    
scrapeFlags' :: FilePath -> IO ScrapedFlags
scrapeFlags' fp = do
  m <- scrapeFlags fp
  return $ case m of
    Nothing -> defaultScrapedFlags
    Just f -> f

defaultScrapedFlags :: ScrapedFlags
defaultScrapedFlags = ScrapedFlags True
