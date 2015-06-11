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
  , performStage = parseAndToast []
  , formatStage = F.format . ppDefault 
  }

type ImportStack = [FilePath]

parseAndToast :: ImportStack -> FilePath -> InsomniaMain Toplevel
parseAndToast imps fp =
  -- TODO: error out if imports recursively visit this same file again
  do
    surfaceAst <- parseInsomniaFile imps fp
    ToAST.toAST surfaceAst (importHandler $ fp:imps)

parseInsomniaFile :: ImportStack -> FilePath -> InsomniaMain Surface.Toplevel
parseInsomniaFile imps fp = do
  result <- lift $ P.parseFile fp
  case result of
   Left err -> showErrorAndDie "parsing" err
   Right surfaceAst -> return surfaceAst

importHandler :: ImportStack
                 -> Surface.ImportFileSpec
                 -> InsomniaMain (Either ToAST.ImportFileError Surface.Toplevel)
importHandler imps s = do
  let fp = Surface.importFileSpecPath s
  surfStx <- parseInsomniaFile imps fp
  return (Right surfStx)
