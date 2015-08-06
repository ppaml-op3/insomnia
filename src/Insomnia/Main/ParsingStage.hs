{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Main.ParsingStage where

import Control.Monad.Trans

import qualified Data.Format as F

import Insomnia.Main.Monad
import Insomnia.Main.Stage

import qualified Pipes

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

parseAndToast :: Pipes.Pipe FilePath Toplevel InsomniaMain ()
parseAndToast = parseInsomniaFile Pipes.>-> do
  surfaceAst <- Pipes.await
  x <- Pipes.lift $ Pipes.runEffect $ ToAST.toAST surfaceAst (showErrorAndDie "resolving names" . show) importHandler
  Pipes.yield x

parseInsomniaFile :: Pipes.Pipe FilePath Surface.Toplevel InsomniaMain ()
parseInsomniaFile = do
  fp <- Pipes.await
  result <- Pipes.lift $ lift $ P.parseFile fp
  case result of
   Left err -> Pipes.lift $ showErrorAndDie "parsing insomnia file" err
   Right surfaceAst -> Pipes.yield surfaceAst

importHandler :: Surface.ImportFileSpec
                 -> InsomniaMain (Either ToAST.ImportFileError Surface.Toplevel)
importHandler s = do
  let fp = Surface.importFileSpecPath s
  x <- Pipes.next (Pipes.yield fp Pipes.>-> parseInsomniaFile)
  case x of
    Left () -> showErrorAndDie "parsing import" ("the import was " ++ fp)
    Right (ans, _) -> return $ Right ans

