{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.InsomniaStages where

import Control.Monad.Reader
import Data.Monoid (Monoid(..), (<>))

import qualified Data.Format as F

import qualified Pipes

import Insomnia.Main.Config
import Insomnia.Main.Monad
import Insomnia.Main.Stage

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

import Insomnia.Main.ParsingStage (parsingStage)
import Insomnia.Main.SaveFinalProductStage (saveFinalProductStage)

parseAndCheck' :: Stage FilePath FOmega.Command
parseAndCheck' =
  parsingStage
  ->->- desugaring
  ->->- checking
  ->->- toFOmega
  ->->- checkFOmega
  ->->- conditionalStage (asks ismCfgEvaluateFOmega) runFOmega

parseAndCheck :: FilePath -> InsomniaMain ()
parseAndCheck fp =
  Pipes.runEffect $ startingFrom fp $ 
  parseAndCheck'
  ->->- compilerDone

parseAndCheckAndGamble :: FilePath -> InsomniaMain ()
parseAndCheckAndGamble fp =
  Pipes.runEffect $ startingFrom fp $
  parseAndCheck'
  ->->- translateToGamble
  ->->- prettyPrintGamble
  ->->- (saveFinalProductStage "Gamble code")
  ->->- compilerDone

desugaring :: Stage Toplevel Toplevel
desugaring = Stage {
  bannerStage = "Desugaring"
  , performStage = do
    t <- Pipes.await
    let t' = IReturn.toplevel t
    Pipes.yield t'
  , formatStage = F.format . ppDefault
  }

checking :: Stage Toplevel Toplevel
checking = Stage {
  bannerStage = "Typechecking"
  , performStage = do
    ast <- Pipes.await
    let tc = TC.runTC $ TC.checkToplevel ast
    (elab, unifState) <- Pipes.lift $ case tc of
      Left err -> showErrorAndDie "typechecking" err
      Right ((elab, _tsum), unifState) -> return (elab, unifState)
    Pipes.lift $ do
      putDebugStrLn "Typechecked OK."
      putDebugStrLn "Unification state:"
      putDebugDoc (F.format (ppDefault unifState)
                   <> F.newline)
    Pipes.yield elab
  , formatStage = F.format . ppDefault
  }

toFOmega :: Stage Toplevel FOmega.Command
toFOmega = Stage {
  bannerStage = "Convert to FΩ"
  , performStage = do
    pgm <- Pipes.await
    let (_sigSummary, tm) = ToF.runToFM $ ToF.toplevel pgm
    Pipes.yield tm
  , formatStage = F.format . ppDefault
}

checkFOmega :: Stage FOmega.Command FOmega.Command
checkFOmega = Stage {
  bannerStage = "Typechecking FΩ"
  , performStage = do
    m <- Pipes.await
    mty <- Pipes.lift $ FCheck.runTC (FCheck.inferCmdTy m)
    Pipes.lift $ case mty of
      Left err -> showErrorAndDie "typechecking FOmega" (show err)
      Right ty -> do
        putDebugStrLn "FOmega type is: "
        putDebugDoc (F.format $ ppDefault ty)
        putDebugStrLn "\n"
    Pipes.yield m
  , formatStage = const mempty
  }

runFOmega :: Stage FOmega.Command FOmega.Command
runFOmega = Stage {
  bannerStage = "Running FΩ"
  , performStage = do
    m <- Pipes.await
    mv <- Pipes.lift $ FOmega.runEvalCommand m
    Pipes.lift $ case mv of
     Left err -> showErrorAndDie "running FOmega" (show err)
     Right v -> do
       putDebugDoc (F.format $ ppDefault v)
    Pipes.yield m
  , formatStage = const mempty
  }

translateToGamble :: Stage  FOmega.Command Gambling.Racket.Module
translateToGamble = Stage {
  bannerStage = "Translating to Gamble"
  , performStage = do
    c <- Pipes.await
    Pipes.yield $ ToGamble.fomegaToGamble "<unnamed>" c
  , formatStage = const mempty
  }

prettyPrintGamble :: Stage Gambling.Racket.Module F.Doc
prettyPrintGamble = Stage {
  bannerStage = "Pretty-printing Gamble code"
  , performStage = do
    m <- Pipes.await
    Pipes.yield $ EmitGamble.emitIt m
  , formatStage = id
  }

