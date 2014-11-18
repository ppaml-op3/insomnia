{-# LANGUAGE ViewPatterns #-}
module Insomnia.Typecheck.Selfify
       (selfifyModelType
       , selfifyTypeDefn
       ) where

import Data.Maybe (mapMaybe)
import Data.Monoid (Monoid(..))

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier (Path(..), Identifier, lastOfPath)
import Insomnia.Types (Con(..), TypeConstructor(..))
import Insomnia.Expr (QVar(..))
import Insomnia.TypeDefn (TypeDefn(..), ConstructorDef(..))
import Insomnia.ModelType (ModelType(..), Signature(..), TypeSigDecl(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.SigOfModelType (signatureOfModelType)

-- | "Selfification" (c.f. TILT) is the process of adding to the current scope
-- a type variable of singleton kind (ie, a module variable standing
-- for a module expression) such that the module variable is given its principal
-- kind (exposes maximal sharing).
selfifyModelType :: Path -> Signature -> TC SelfSig
selfifyModelType pmod msig_ =
  case msig_ of
    UnitSig -> return UnitSelfSig
    ValueSig fld ty msig -> do
      let qvar = QVar (ProjP pmod fld)
      selfSig <- selfifyModelType pmod msig
      return $ ValueSelfSig qvar ty selfSig
    TypeSig fld bnd ->
      U.lunbind bnd $ \((tyId, U.unembed -> tsd), msig) -> do
      let p = ProjP pmod fld
          -- replace the local Con (IdP tyId) way of refering to
          -- this definition in the rest of the signature by
          -- the full projection from the model path.  Also replace the
          -- type constructors
          substVCons = selfifyTypeSigDecl pmod tsd
          substTyCon = [(tyId, TCGlobal p)]
          tsd' = U.substs substTyCon $ U.substs substVCons tsd
          msig' = U.substs substTyCon $ U.substs substVCons msig
      selfSig <- selfifyModelType pmod msig'
      return $ TypeSelfSig (Con p) tsd' selfSig
    SubmodelSig fld bnd ->
      U.lunbind bnd $ \((modId, U.unembed -> modTy), msig) -> do
        let p = ProjP pmod fld
        modSig <- signatureOfModelType modTy
        modSelfSig' <- selfifyModelType p modSig
        let msig' = U.subst modId p msig
        selfSig' <- selfifyModelType pmod msig'
        return $ SubmodelSelfSig p modSelfSig' selfSig'

selfSigToSignature :: SelfSig -> TC Signature
selfSigToSignature UnitSelfSig = return UnitSig
selfSigToSignature (ValueSelfSig (QVar valuePath) ty selfSig) = do
  let fieldName = lastOfPath valuePath
  sig <- selfSigToSignature selfSig
  return $ ValueSig fieldName ty sig
selfSigToSignature (TypeSelfSig (Con typePath) tsd selfSig) = do
  let fieldName = lastOfPath typePath
  freshId <- U.lfresh (U.s2n fieldName)
  sig <- selfSigToSignature selfSig
  return $ TypeSig fieldName (U.bind (freshId, U.embed tsd) sig)
selfSigToSignature (SubmodelSelfSig path subSelfSig selfSig) = do
  let fieldName = lastOfPath path
  freshId <- U.lfresh (U.s2n fieldName)
  subSig <- selfSigToSignature subSelfSig
  sig <- selfSigToSignature selfSig
  let subModTy = SigMT subSig
  return $ SubmodelSig fieldName (U.bind (freshId, U.embed subModTy) sig)

selfifyTypeSigDecl :: Path -> TypeSigDecl -> [(Identifier, Path)]
selfifyTypeSigDecl pmod tsd =
  case tsd of
    AbstractTypeSigDecl _k -> mempty
    ManifestTypeSigDecl defn -> selfifyTypeDefn pmod defn
    AliasTypeSigDecl _alias -> mempty

-- | Given the path to a type defintion and the type definition, construct
-- a substitution that replaces unqualified references to the components of
-- the definition (for example the value constructors of an algebraic datatype)
-- by their qualified names with respect to the given path.
selfifyTypeDefn :: Path -> TypeDefn -> [(Identifier, Path)]
selfifyTypeDefn _pmod (EnumDefn _) = []
selfifyTypeDefn pmod (DataDefn bnd) = let
  (_, constrDefs) = UU.unsafeUnbind bnd
  cs = map (\(ConstructorDef c _) -> c) constrDefs
  in mapMaybe (mkSubst pmod) cs
  where
    mkSubst :: Path -> Con -> Maybe (Identifier, Path)
    mkSubst p (Con (IdP short)) = let fld = U.name2String short
                                      long = ProjP p fld
                                  in Just (short, long)
    mkSubst _ _                 = Nothing
