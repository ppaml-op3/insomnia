module Main where

import qualified System.FilePath.Glob as Glob

import Test.Tasty (TestTree, testGroup, defaultMain)
import InsomniaProvider (testInsomnia)

makeInsomniaTests :: FilePath -> Glob.Pattern -> IO TestTree
makeInsomniaTests baseDir pat = do
  files <- Glob.globDir1 pat baseDir
  return $ testGroup ("run Insomnia on " ++ show pat ++ " in " ++ show baseDir)
    $ map runInsomniaOn files
  where
    runInsomniaOn f = testInsomnia ("compiling " ++ show f) f

main = do
  t <- makeInsomniaTests "examples/" (Glob.compile "*.ism")
  defaultMain t
