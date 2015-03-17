{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified System.IO as IO

import Control.Monad.Reader

import Data.Monoid (Monoid(..), (<>))

import Data.Format (Format)
import qualified Data.Format as F

import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import Insomnia.Toplevel (Toplevel)
import Insomnia.Typecheck
import Insomnia.Pretty
import qualified Insomnia.IReturn as IReturn
import qualified Insomnia.ToF as ToF
import qualified FOmega.Syntax as FOmega
import qualified FOmega.Check as FCheck

main :: IO ()
main = do
  act <- processArguments
  case act of
    Typecheck fp -> runInsomniaMain (parseAndCheck fp) defaultConfig
    HelpUsage -> printUsage

type InsomniaMain a = ReaderT InsomniaMainConfig IO a

data InsomniaMainConfig = InsomniaMainConfig {
  ismCfgDebugOut :: IO.Handle -- ^ handle to use for debug output
  , ismCfgErrorOut :: IO.Handle -- ^ handle to use for error output
  }

runInsomniaMain :: InsomniaMain a -> InsomniaMainConfig -> IO a
runInsomniaMain = runReaderT 

defaultConfig :: InsomniaMainConfig
defaultConfig = InsomniaMainConfig {
  ismCfgDebugOut = IO.stdout
  , ismCfgErrorOut = IO.stderr
  }

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
printUsage = putStrLn "Usage: insomnia [FILE | --help]"

parseAndCheck :: FilePath -> InsomniaMain ()
parseAndCheck fp =
  startingFrom fp
  $ parsing
  ->->- desugaring
  ->->- checking
  ->->- toFOmega
  ->->- checkFOmega
  ->->- compilerDone

parsing :: Stage FilePath Toplevel
parsing = Stage {
  bannerStage = "Parsing"
  , performStage = \fp -> do
     result <- lift $ P.parseFile fp
     case result of
       Left err -> showErrorAndDie "parsing" err
       Right surfaceAst -> return (ToAST.toAST surfaceAst)
  , formatStage = F.format . ppDefault 
  }

desugaring :: Stage Toplevel Toplevel
desugaring = Stage {
  bannerStage = "Desugaring"
  , performStage = \t ->
     let t' = IReturn.toplevel t
     in return t'
  , formatStage = F.format . ppDefault
  }

checking :: Stage Toplevel Toplevel
checking = Stage {
  bannerStage = "Typechecking"
  , performStage = \ast -> do
    let tc = runTC $ checkToplevel ast
    (elab, m) <- case tc of
      Left err -> showErrorAndDie "typechecking" err
      Right ans -> return ans
    putDebugStrLn "Typechecked OK."
    putDebugStrLn "Unification state:"
    putDebugDoc (F.format (ppDefault m)
                 <> F.newline)
    return elab
  , formatStage = F.format . ppDefault
  }

toFOmega :: Stage Toplevel FOmega.Term
toFOmega = Stage {
  bannerStage = "Convert to FΩ"
  , performStage = \pgm ->
    let tm = ToF.runToFM $ ToF.toplevel pgm
    in return tm
  , formatStage = F.format . ppDefault
}

checkFOmega :: Stage FOmega.Term FOmega.Term
checkFOmega = Stage {
  bannerStage = "Typechecking FΩ"
  , performStage = \m -> do
    mty <- FCheck.runTC (FCheck.inferTy m)
    lift $ case mty of
      Left err -> putStrLn ("typechecking FOmega failed: " ++ show err)
      Right ty -> do
        putStrLn "FOmega type is: "
        F.putStrDoc (F.format $ ppDefault ty)
        putStrLn "\n"
    return m
  , formatStage = const mempty
  }

data Stage a b = Stage { bannerStage :: F.Doc 
                       , performStage :: a -> InsomniaMain b
                       , formatStage :: b -> F.Doc }

(->->-) :: Stage a b -> Stage b c -> Stage a c
stage1 ->->- stage2 = Stage {
  bannerStage = bannerStage stage1
  , performStage = \x -> do
    y <- performStage stage1 x
    putDebugDoc (formatStage stage1 y <> F.newline)
    putDebugStrLn "--------------------✂✄--------------------"
    putDebugDoc (bannerStage stage2 <> F.newline)
    performStage stage2 y
  , formatStage = formatStage stage2
  }

infixr 6 ->->-

compilerDone :: Stage a ()
compilerDone = Stage { bannerStage = mempty
                     , performStage = const (return ())
                     , formatStage = mempty
                     }

startingFrom :: a -> Stage a () -> InsomniaMain ()
startingFrom a stages = do
  putDebugDoc (bannerStage stages <> F.newline)
  performStage stages a

showErrorAndDie :: (Format err) => String -> err -> InsomniaMain a
showErrorAndDie phase msg = do
  putErrorStrLn $ "Encountered error while " ++ phase
  putErrorDoc (F.format msg <> F.newline)
  lift $ exitFailure

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
