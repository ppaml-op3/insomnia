{-# LANGUAGE ViewPatterns #-}
module Insomnia.ToF.Builtins where

import Control.Monad

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Common.ModuleKind
import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.Types (Type)
import Insomnia.Expr (QVar(..))

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F
import qualified FOmega.SubSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Type (type')
import Insomnia.ToF.ModuleType (mkAbstractModuleSig)

import qualified FOmega.Primitives as Primitives

data BuiltinsModuleBinding =
  BuiltinsValueBinding !QVar !Type
  | BuiltinsSubmodule ![(F.Field, BuiltinsModuleBinding)]

looksLikeBuiltin :: Maybe Path -> ModuleType -> Maybe [(F.Field, BuiltinsModuleBinding)]
looksLikeBuiltin (Just p) (SigMT (SigV sig ModuleMK)) =
   looksLikeBuiltinSig p sig
looksLikeBuiltin _ _ = Nothing

looksLikeBuiltinSig :: Path -> Signature -> Maybe [(F.Field, BuiltinsModuleBinding)]
looksLikeBuiltinSig p UnitSig = return []
looksLikeBuiltinSig p (TypeSig {}) = mzero
looksLikeBuiltinSig p (SubmoduleSig f bnd) = do
  let ((_ident, U.unembed -> modTy), rest) = UU.unsafeUnbind bnd
  subMod <- looksLikeBuiltin (Just $ ProjP p f) modTy
  rest' <- looksLikeBuiltinSig p rest
  return $ (F.FUser f, BuiltinsSubmodule subMod) : rest'
looksLikeBuiltinSig p (ValueSig f t rest) = do
  let q = QVar p f
  guard (looksLikeBuiltinQVar q)
  rest' <- looksLikeBuiltinSig p rest
  return $ (F.FUser f, BuiltinsValueBinding q t) : rest'

looksLikeBuiltinQVar :: QVar -> Bool
looksLikeBuiltinQVar q =
  let v = builtinNameFromQVar q
  in Primitives.isPrimitive v

builtinNameFromQVar :: QVar -> F.Var
builtinNameFromQVar (QVar p f) =
  U.s2n $ p2s $ ProjP p f
  where
    p2s (IdP nm) = U.name2String nm
    p2s (ProjP p' f') = p2s p' ++ "." ++ f'

makeBuiltinsModule :: ToF m
                      => [(F.Field, BuiltinsModuleBinding)]
                      -> m (F.AbstractSig, F.Term)
makeBuiltinsModule fbmbs = do
  (sig, fields) <- makeBuiltinsModuleBindings fbmbs
  return (mkAbstractModuleSig ([], sig), F.Record fields)

makeBuiltinsModuleBindings :: ToF m
                              => [(F.Field, BuiltinsModuleBinding)]
                              -> m ([(F.Field, F.SemanticSig)],
                                    [(F.Field, F.Term)])
makeBuiltinsModuleBindings fbmbs =
  liftM unzip $ forM fbmbs $ \(fld, bmb) ->
  case bmb of
   BuiltinsValueBinding q ty -> do
     (ty', _) <- type' ty
     let qv = builtinNameFromQVar q
         m = F.V qv -- builtins looks like funny free names.
     return ((fld, F.ValSem ty'), (fld, F.valSemTerm m))
   BuiltinsSubmodule subBmbs -> do
     (subSig, subFields) <- makeBuiltinsModuleBindings subBmbs
     return ((fld, F.ModSem subSig), (fld, F.Record subFields))
