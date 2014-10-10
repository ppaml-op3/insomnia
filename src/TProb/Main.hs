module TProb.Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)

import Data.Format (Format)
import qualified Data.Format as F

import TProb.Parse
import TProb.Typecheck


main :: IO ()
main = do
  act <- processArguments
  case act of
    Typecheck fp -> parseAndCheck fp
    HelpUsage -> printUsage


data Command =
  Typecheck !FilePath
  | HelpUsage

processArguments :: IO Command
processArguments = do
  args <- getArgs
  case args of
    [arg] | arg == "--help" -> return HelpUsage
          | otherwise -> return $ Typecheck arg
    _ -> return HelpUsage

printUsage :: IO ()
printUsage = putStrLn "Usage: tprob [FILE | --help]"

parseAndCheck :: FilePath -> IO ()
parseAndCheck fp = do
  result <- parseFile fp
  ast <- case result of
    Left err -> showErrorAndDie "parsing" err
    Right ast -> return ast
  let
    tc = runTC $ checkModule ast
  _elab <- case tc of
    Left err -> showErrorAndDie "typechecking" err
    Right elab -> return elab
  putStrLn "Typechecked OK."

showErrorAndDie :: (Format err) => String -> err -> IO a
showErrorAndDie phase msg = do
  putStrLn $ "Encountered error while " ++ phase
  F.putStrDoc (F.format msg)
  exitFailure
