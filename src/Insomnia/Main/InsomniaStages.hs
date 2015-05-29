{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.InsomniaStages where

import Control.Monad.Reader
import Data.Monoid (Monoid(..), (<>))

import qualified Data.Format as F

import Insomnia.Main.Config
import Insomnia.Main.Monad
import Insomnia.Main.Stage

import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import Insomnia.Toplevel (Toplevel)
import Insomnia.Typecheck as TC 
import Insomnia.Pretty
import qualified Insomnia.IReturn as IReturn
import qualified Insomnia.ToF as ToF
import qualified FOmega.Syntax as FOmega
import qualified FOmega.Check as FCheck
import qualified FOmega.Eval as FOmega

import qualified Gambling.FromF as ToGamble
import qualified Gambling.Emit as EmitGamble
import qualified Gambling.Racket

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
    let tc = TC.runTC $ TC.checkToplevel ast
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


