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
import qualified FOmega.Eval as FOmega

import qualified Gambling.FromF as ToGamble
import qualified Gambling.Emit as EmitGamble
import qualified Gambling.Racket

main :: IO ()
main = do
  act <- processArguments
  case act of
    Typecheck fp -> runInsomniaMain (parseAndCheck fp) defaultConfig
    Gamble fp -> runInsomniaMain (parseAndCheckAndGamble fp)
                                 (defaultConfig { ismCfgEvaluateFOmega = False })
    HelpUsage -> printUsage

type InsomniaMain a = ReaderT InsomniaMainConfig IO a

data InsomniaMainConfig = InsomniaMainConfig {
  ismCfgDebugOut :: IO.Handle -- ^ handle to use for debug output
  , ismCfgErrorOut :: IO.Handle -- ^ handle to use for error output
  , ismCfgEvaluateFOmega :: Bool -- ^ if True, run the FOmega code, ow just typecheck it.
  }

runInsomniaMain :: InsomniaMain a -> InsomniaMainConfig -> IO a
runInsomniaMain = runReaderT 

defaultConfig :: InsomniaMainConfig
defaultConfig = InsomniaMainConfig {
  ismCfgDebugOut = IO.stdout
  , ismCfgErrorOut = IO.stderr
  , ismCfgEvaluateFOmega = True
  }

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

parseAndCheck' :: Stage FilePath FOmega.Command
parseAndCheck' =
  parsing
  ->->- desugaring
  ->->- checking
  ->->- toFOmega
  ->->- checkFOmega
  ->->- conditionalStage (asks ismCfgEvaluateFOmega) runFOmega

parseAndCheck :: FilePath -> InsomniaMain ()
parseAndCheck fp =
  startingFrom fp $ 
  parseAndCheck'
  ->->- compilerDone

parseAndCheckAndGamble :: FilePath -> InsomniaMain ()
parseAndCheckAndGamble fp =
  startingFrom fp $
  parseAndCheck'
  ->->- translateToGamble
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

toFOmega :: Stage Toplevel FOmega.Command
toFOmega = Stage {
  bannerStage = "Convert to FΩ"
  , performStage = \pgm ->
    let tm = ToF.runToFM $ ToF.toplevel pgm
    in return tm
  , formatStage = F.format . ppDefault
}

checkFOmega :: Stage FOmega.Command FOmega.Command
checkFOmega = Stage {
  bannerStage = "Typechecking FΩ"
  , performStage = \m -> do
    mty <- FCheck.runTC (FCheck.inferCmdTy m)
    case mty of
      Left err -> showErrorAndDie "typechecking FOmega" (show err)
      Right ty -> do
        putDebugStrLn "FOmega type is: "
        putDebugDoc (F.format $ ppDefault ty)
        putDebugStrLn "\n"
    return m
  , formatStage = const mempty
  }

runFOmega :: Stage FOmega.Command FOmega.Command
runFOmega = Stage {
  bannerStage = "Running FΩ"
  , performStage = \m -> do
    mv <- FOmega.runEvalCommand m
    case mv of
     Left err -> showErrorAndDie "running FOmega" (show err)
     Right v -> do
       putDebugDoc (F.format $ ppDefault v)
    return m
  , formatStage = const mempty
  }

translateToGamble :: Stage  FOmega.Command Gambling.Racket.Module
translateToGamble = Stage {
  bannerStage = "Translating to Gamble"
  , performStage = return . ToGamble.fomegaToGamble "<unnamed>"
  , formatStage = EmitGamble.emitIt 
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

conditionalStage :: InsomniaMain Bool -> Stage a a -> Stage a a
conditionalStage shouldRun stage =
  Stage { bannerStage = bannerStage stage
        , performStage = \inp -> do
          b <- shouldRun
          case b of
           True -> performStage stage inp
           False -> do
             putErrorDoc ("SKIPPED " <> bannerStage stage)
             return inp
        , formatStage = formatStage stage
        }
            

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
