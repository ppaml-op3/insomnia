{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.Selfify
       (selfifySigV
       , selfifySignature
       , selfifyTypeDefn
       ) where

import Data.Monoid (Monoid(..))
import Data.Traversable (Traversable(..))

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier (Path(..), lastOfPath)
import Insomnia.Types (TypeConstructor(..), TypePath(..))
import Insomnia.Expr (QVar(..))
import Insomnia.TypeDefn (TypeDefn(..), ValConName,
                          ValConPath(..), ValueConstructor(..),
                          ConstructorDef(..))
import Insomnia.ModuleType (ModuleType(..), Signature(..),
                            SigV,
                            TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.SigOfModuleType (signatureOfModuleType)

selfifySigV :: Path -> SigV Signature -> TC (SigV SelfSig)
selfifySigV = traverse . selfifySignature 

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
          substVCons = selfifyTypeSigDecl pmod tsd
          substTyCon = [(tyId, TCGlobal p)]
          tsd' = U.substs substTyCon $ U.substs substVCons tsd
          msig' = U.substs substTyCon $ U.substs substVCons msig
      selfSig <- selfifySignature pmod msig'
      return $ TypeSelfSig p tsd' selfSig
    SubmoduleSig fld bnd ->
      U.lunbind bnd $ \((modId, U.unembed -> modTy), msig) -> do
        let p = ProjP pmod fld
        subSigV <- signatureOfModuleType modTy
        subSigV' <- selfifySigV p subSigV
        let msig' = U.subst modId p msig
        selfSig' <- selfifySignature pmod msig'
        return $ SubmoduleSelfSig p subSigV' selfSig'

selfSigToSigV :: SigV SelfSig -> TC (SigV Signature)
selfSigToSigV = traverse selfSigToSignature

selfSigToSignature :: SelfSig -> TC Signature
selfSigToSignature UnitSelfSig = return UnitSig
selfSigToSignature (ValueSelfSig (QVar _modulePath fieldName) ty selfSig) = do
  sig <- selfSigToSignature selfSig
  return $ ValueSig fieldName ty sig
selfSigToSignature (TypeSelfSig typePath tsd selfSig) = do
  let (TypePath _ fieldName) = typePath
  freshId <- U.lfresh (U.s2n fieldName)
  sig <- selfSigToSignature selfSig
  return $ TypeSig fieldName (U.bind (freshId, U.embed tsd) sig)
selfSigToSignature (SubmoduleSelfSig path subSelfSigV selfSig) = do
  let fieldName = lastOfPath path
  freshId <- U.lfresh (U.s2n fieldName)
  subSigV <- selfSigToSigV subSelfSigV
  sig <- selfSigToSignature selfSig
  let subModTy = SigMT subSigV
  return $ SubmoduleSig fieldName (U.bind (freshId, U.embed subModTy) sig)

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
