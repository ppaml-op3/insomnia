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

newtype InsomniaTest = InsomniaTest { insomniaTestFilePath :: FilePath }
                       deriving (Show, Typeable)

instance IsTest InsomniaTest where
  run _opts (InsomniaTest fp) _reportProgress = do
    IOTemp.withTempFile "dist/test" "ism." $ \logFP logHandle -> do
      (runInsomnia logHandle fp >> return (testPassed ""))
      `Exn.catch` (\e ->
                    case e of
                     ExitCode.ExitSuccess -> return $ testPassed ""
                     ExitCode.ExitFailure _ -> do
                       IO.hClose logHandle
                       log <- IO.readFile logFP
                       return $ testFailed $ log)

  testOptions = Tagged []

runInsomnia :: IO.Handle -> FilePath -> IO ()
runInsomnia logHandle fp = 
  Insomnia.runInsomniaMain (Insomnia.parseAndCheck fp)
  $ Insomnia.defaultConfig {
    Insomnia.ismCfgDebugOut = logHandle
    , Insomnia.ismCfgErrorOut = logHandle
    }

testInsomnia :: TestName -> FilePath -> TestTree
testInsomnia name = singleTest name . InsomniaTest
