{-# LANGUAGE FlexibleContexts #-}
module Insomnia.SurfaceSyntax.Interactive where

import qualified Data.Text as T

import Data.Format (putStrDoc, docToString, Format(format))

import qualified Unbound.Generics.LocallyNameless as U

import FOmega.Syntax as F
import FOmega.SemanticSig as F
import FOmega.Check as F

import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import qualified Insomnia.SurfaceSyntax.ToastMonad as ToAST
import qualified Insomnia.ToF as ToF
import Insomnia.Typecheck.Env as TC
import Insomnia.Typecheck.Module as TC
import Insomnia.Identifier (Path(..))
import Insomnia.Pretty (ppDefault)


-- | Parse a module type expression (most commonly a signature),
-- convert it to an Insomnia AST, then convert it to an FOmega
-- abstract semantic signature.  Note that no Insomnia typechecking is performed,
-- so the FOmega translation will fail if no translation is possible.
--
-- >>> Insomnia.SurfaceSyntax.Interactive.moduleType "{ type T :: *\n  sig x :: T -> T }"
-- AbstractSig (<[(T,{KType})]> ModSem [(FUser "T",TypeSem (TV 0@0) KType),(FUser "x",ValSem (TApp (TApp (TLam (<(α,{KType})> TLam (<(β,{KType})> TArr (TV 1@0) (TV 0@0)))) (TV 0@0)) (TV 0@0)))])
moduleType :: T.Text -> IO F.AbstractSig
moduleType txt = do
  let okOrErr = P.parseText "-" txt P.moduleTypeExpr
  syn <- case okOrErr of
   Left err -> fail (docToString $ format err)
   Right ok -> return ok
  modTy <- ToAST.feedTA (ToAST.moduleType syn) interactiveImportHandler ToAST.toASTbaseCtx
  let abstr = ToF.runToFM $ ToF.moduleType modTy
  return abstr

interactiveImportHandler :: a -> IO b
interactiveImportHandler _ =
  fail "did not expect the import handler to be called"

-- | >>> moduleExpr "{ module X :: {\n type T :: *\n sig t :: T -> T\n } {\n type T = Int\n sig t :: T -> T\n fun t x = x } }"
moduleExpr :: T.Text -> IO (F.AbstractSig, F.Term)
moduleExpr txt = do
  let okOrErr = P.parseText "-" txt P.bigExpr
  syn <- case okOrErr of
    Left err -> fail (docToString $ format err)
    Right ok -> return ok
  modExpr <- ToAST.feedTA (ToAST.expectBigExprModule syn) interactiveImportHandler ToAST.toASTbaseCtx
  let tc = TC.runTC $ TC.inferModuleExpr (IdP $ U.s2n "M") modExpr (\modExpr' _ -> return modExpr')
  modExpr' <- case tc of
    Left err -> fail (docToString $ format err)
    Right (ok, _) -> return ok
  putStrDoc (format $ ppDefault modExpr')
  putStrLn "\n-----"
  let z@(_, tm) = ToF.runToFM $ ToF.moduleExpr Nothing modExpr'
  putStrDoc (format $ ppDefault tm)
  putStrLn "\n"
  mty <- F.runTC (F.inferTy tm)
  case mty of
   Left err -> putStrLn ("typechecking FOmega failed: " ++ show err)
   Right ty -> do
     putStrLn "FOmega type is: "
     putStrDoc (format $ ppDefault ty)
     putStrLn "\n-------"
  return z
