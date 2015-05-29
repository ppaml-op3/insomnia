module Insomnia.Main.Command where

import System.Environment (getArgs)

data Command =
  Typecheck !FilePath
  | Gamble !FilePath
  | HelpUsage

processArguments :: IO Command
processArguments = do
  args <- getArgs
  case args of
    [arg] | arg == "--help" -> return HelpUsage
          | otherwise -> return $ Typecheck arg
    ["-c", arg] -> return $ Gamble arg
    _ -> return HelpUsage

printUsage :: IO ()
printUsage = putStrLn "Usage: insomnia [[-c] FILE | --help]"

