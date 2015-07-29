{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.ParsingStage where

import Control.Monad.Trans

import qualified Data.Format as F

import Insomnia.Main.Monad
import Insomnia.Main.Stage

import qualified Insomnia.SurfaceSyntax.Syntax as Surface
import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import qualified Insomnia.SurfaceSyntax.ToastMonad as ToAST

import Insomnia.Toplevel (Toplevel)
import Insomnia.Pretty

parsingStage :: Stage FilePath Toplevel
parsingStage = Stage {
  bannerStage = "Parsing"
  , performStage = parseAndToast
  , formatStage = F.format . ppDefault 
  }

parseAndToast :: FilePath -> InsomniaMain Toplevel
parseAndToast fp = do
  do
    surfaceAst <- parseInsomniaFile fp
    ToAST.toAST surfaceAst (showErrorAndDie "resolving names" . show) importHandler

parseInsomniaFile :: FilePath -> InsomniaMain Surface.Toplevel
parseInsomniaFile fp = do
  result <- lift $ P.parseFile fp
  case result of
   Left err -> showErrorAndDie "parsing" err
   Right surfaceAst -> return surfaceAst

importHandler :: Surface.ImportFileSpec
                 -> InsomniaMain (Either ToAST.ImportFileError Surface.Toplevel)
importHandler s = do
  let fp = Surface.importFileSpecPath s
  surfStx <- parseInsomniaFile fp
  return (Right surfStx)
