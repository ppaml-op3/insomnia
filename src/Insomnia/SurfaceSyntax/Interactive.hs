{-# LANGUAGE FlexibleContexts #-}
module Insomnia.SurfaceSyntax.Interactive where

import qualified Data.Text as T

import Data.Format (docToString, Format(format))

import FOmega.SemanticSig as F

import qualified Insomnia.SurfaceSyntax.Parse as P
import qualified Insomnia.SurfaceSyntax.ToAST as ToAST
import qualified Insomnia.ToF as ToF

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
  let modTy = ToAST.runToAST ToAST.toASTbaseCtx (ToAST.moduleType syn)
      abstr = ToF.runToFM $ ToF.moduleType modTy
  return abstr
