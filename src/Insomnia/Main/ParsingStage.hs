{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.ParsingStage where

import Control.Monad.Trans

import qualified Data.Format as F

import Insomnia.Main.Monad
import Insomnia.Main.Stage

import qualified Insomnia.SurfaceSyntax.Syntax as Surface
import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST

import Insomnia.Toplevel (Toplevel)
import Insomnia.Pretty

parsingStage :: Stage FilePath Toplevel
parsingStage = Stage {
  bannerStage = "Parsing"
  , performStage = parseAndToast
  , formatStage = F.format . ppDefault 
  }

parseAndToast :: FilePath -> InsomniaMain Toplevel
parseAndToast fp =
  -- TODO: wrap this whole computation so that we:
  -- 1. record that we're currently parsing the given file;
  -- 2. error out if imports recursively visit this same file again
  -- 2. mention the trail of imports if there's an error;
  -- 3. memoize the parsing result for this file and return it if needed again.
  do
    result <- lift $ P.parseFile fp
    case result of
     Left err -> showErrorAndDie "parsing" err
     Right surfaceAst ->
       ToAST.toAST surfaceAst importHandler

importHandler :: Surface.ImportFileSpec -> InsomniaMain (Either ToAST.ImportFileError Toplevel)
importHandler s = do
  let fp = Surface.importFileSpecPath s
  tl <- parseAndToast fp
  return (Right tl)
