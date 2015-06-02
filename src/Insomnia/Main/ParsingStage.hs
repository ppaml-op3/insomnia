{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.ParsingStage where

import Control.Monad.Trans

import qualified Data.Format as F

import Insomnia.Main.Monad
import Insomnia.Main.Stage

import qualified Insomnia.SurfaceSyntax.Syntax as Surface
import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST

import Insomnia.Toplevel (Toplevel, ToplevelItem)
import Insomnia.Pretty

parsingStage :: Stage FilePath Toplevel
parsingStage = Stage {
  bannerStage = "Parsing"
  , performStage = parseAndToast
  , formatStage = F.format . ppDefault 
  }

parseAndToast :: FilePath -> InsomniaMain Toplevel
parseAndToast fp = do
  result <- lift $ P.parseFile fp
  case result of
   Left err -> showErrorAndDie "parsing" err
   Right surfaceAst ->
     ToAST.toAST surfaceAst importHandler

importHandler :: Surface.ImportFileSpec -> InsomniaMain (Either ToAST.ImportFileError ToplevelItem)
importHandler s = do
  let fp = Surface.importFileSpecPath s
  tl <- parseAndToast fp
  return $ Left $ ToAST.ImportFileError $ "successfully read " ++ (show fp) ++ " but aborting anyway because this is a test"
