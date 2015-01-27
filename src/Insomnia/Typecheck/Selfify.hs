{-# LANGUAGE ViewPatterns, OverloadedStrings #-}
module Insomnia.Typecheck.Selfify
       ( selfifySignature
       , selfifyTypeDefn
       ) where

import Data.Monoid (Monoid(..))

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Path(..))
import Insomnia.Types (TypeConstructor(..), TypePath(..))
import Insomnia.Expr (QVar(..))
import Insomnia.TypeDefn (TypeDefn(..), ValConName,
                          ValConPath(..), ValueConstructor(..),
                          ConstructorDef(..))
import Insomnia.ModuleType (Signature(..),
                            SigV(..),
                            ModuleTypeNF(..),
                            TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.WhnfModuleType (whnfModuleType)
import {-# SOURCE #-} Insomnia.Typecheck.ExtendModuleCtx (extendTypeSigDeclCtx, extendModuleCtx)

-- | "Selfification" (c.f. TILT) is the process of adding to the current scope
-- a type variable of singleton kind (ie, a module variable standing
-- for a module expression) such that the module variable is given its principal
-- kind (exposes maximal sharing).
selfifySignature :: Path -> Signature -> TC SelfSig
selfifySignature pmod msig_ =
  case msig_ of
    UnitSig -> return UnitSelfSig
    ValueSig fld ty msig -> do
      let qvar = QVar pmod fld
      selfSig <- selfifySignature pmod msig
      return $ ValueSelfSig qvar ty selfSig
    TypeSig fld bnd ->
      U.lunbind bnd $ \((tyId, U.unembed -> tsd), msig) -> do
      let p = TypePath pmod fld
          -- replace the local Con (IdP tyId) way of refering to
          -- this definition in the rest of the signature by
          -- the full projection from the model path.  Also replace the
          -- type constructors
          tcon = TCGlobal p
          substVCons = selfifyTypeSigDecl pmod tsd
          substTyCon = [(tyId, tcon)]
          tsd' = U.substs substTyCon $ U.substs substVCons tsd
          msig' = U.substs substTyCon $ U.substs substVCons msig
      selfSig <- extendTypeSigDeclCtx tcon tsd $ selfifySignature pmod msig'
      return $ TypeSelfSig p tsd' selfSig
    SubmoduleSig fld bnd ->
      U.lunbind bnd $ \((modId, U.unembed -> modTy), msig) -> do
        let p = ProjP pmod fld
        mtnf <- whnfModuleType modTy
        case mtnf of
         (SigMTNF (SigV subSig ModuleMK)) -> do
           subSelfSig <- selfifySignature p subSig
           let msig' = U.subst modId p msig
           selfSig' <- extendModuleCtx subSelfSig $ selfifySignature pmod msig'
           return $ SubmoduleSelfSig p subSelfSig selfSig'
         (SigMTNF (SigV _ ModelMK)) -> do
           let msig' = U.subst modId p msig
           selfSig' <- selfifySignature pmod msig'
           return $ GenerativeSelfSig p mtnf selfSig'
         (FunMTNF {}) -> do
           let msig' = U.subst modId p msig
           selfSig' <- selfifySignature pmod msig'
           return $ GenerativeSelfSig p mtnf selfSig'

selfifyTypeSigDecl :: Path -> TypeSigDecl -> [(ValConName, ValueConstructor)]
selfifyTypeSigDecl pmod tsd =
  case tsd of
    AbstractTypeSigDecl _k -> mempty
    ManifestTypeSigDecl defn -> selfifyTypeDefn pmod defn
    AliasTypeSigDecl _alias -> mempty

-- | Given the path to a type defintion and the type definition, construct
-- a substitution that replaces unqualified references to the components of
-- the definition (for example the value constructors of an algebraic datatype)
-- by their qualified names with respect to the given path.
selfifyTypeDefn :: Path -> TypeDefn -> [(ValConName, ValueConstructor)]
selfifyTypeDefn _pmod (EnumDefn _) = []
selfifyTypeDefn pmod (DataDefn bnd) = let
  (_, constrDefs) = UU.unsafeUnbind bnd
  cs = map (\(ConstructorDef c _) -> c) constrDefs
  in map (mkSubst pmod) cs
  where
    mkSubst :: Path -> ValConName -> (ValConName, ValueConstructor)
    mkSubst p short =
      let fld = U.name2String short
          long = ValConPath p fld
      in (short, VCGlobal long)
