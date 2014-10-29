{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Typecheck "model type" expressions.
module Insomnia.Typecheck.ModelType where

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Field, Path(..))
import Insomnia.Types (Con(..), Kind(..))
import Insomnia.ModelType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, checkTypeAlias)
import Insomnia.Typecheck.ExtendModelCtx (extendTypeSigDeclCtx, extendModelCtx)
import Insomnia.Typecheck.Selfify (selfifyModelType)

-- | Check that the given model type expression is well-formed, and
-- return both the model type expression and the signature that it
-- "evaluates" to.
checkModelType :: ModelType -> TC (ModelType, Signature)
checkModelType (SigMT msig) = do
  msig' <- checkSignature Nothing msig
  return (SigMT msig', msig')
checkModelType (IdentMT ident) = do
  msig <- lookupModelType ident
  return (IdentMT ident, msig)

checkSignature :: Maybe Path -> Signature -> TC Signature
checkSignature mpath_ = flip (checkSignature' mpath_) ensureNoDuplicateFields
  where
    -- TODO: actually check that the field names are unique.
    ensureNoDuplicateFields :: (Signature, [Field]) -> TC Signature
    ensureNoDuplicateFields (sig, _flds) = return sig

    checkSignature' :: Maybe Path
                       -> Signature -> ((Signature, [Field]) -> TC Signature)
                       -> TC Signature
    checkSignature' _mpath UnitSig kont = kont (UnitSig, [])
    checkSignature' mpath (ValueSig fld ty sig) kont = do
        ty' <- checkType ty KType
        checkSignature' mpath sig $ \(sig', flds) ->
          kont (ValueSig fld ty' sig', fld:flds)
    checkSignature' mpath (TypeSig fld bnd) kont =
      U.lunbind bnd $ \((tyident, U.unembed -> tsd), sig) -> do
        let dcon = Con (IdP tyident)
        -- guardDuplicateDConDecl dcon -- can't happen
        tsd' <- checkTypeSigDecl dcon tsd
        extendTypeSigDeclCtx dcon tsd
          $ checkSignature' mpath sig $ \(sig', flds) ->
           kont (TypeSig fld $ U.bind (tyident, U.embed tsd') sig', fld:flds)
    checkSignature' mpath (SubmodelSig fld bnd) kont =
      U.lunbind bnd $ \((modIdent, U.unembed -> modTy), sig) -> do
        let modPath = mpathAppend mpath fld
        (modTy', modSig) <- checkModelType modTy
        selfSig <- selfifyModelType modPath modSig
        let sig' = U.subst modIdent modPath sig
        extendModelCtx selfSig
          $ checkSignature' mpath sig' $ \(sig'', flds) ->
          kont (SubmodelSig fld $ U.bind (modIdent, U.embed modTy') sig''
                , fld:flds)
        

mpathAppend :: Maybe Path -> Field -> Path
mpathAppend Nothing fld = IdP (U.s2n fld)
mpathAppend (Just p) fld = ProjP p fld

checkTypeSigDecl :: Con -> TypeSigDecl -> TC TypeSigDecl
checkTypeSigDecl dcon tsd =
  case tsd of
    ManifestTypeSigDecl defn -> do
      (defn', _) <-  checkTypeDefn dcon defn
      return $ ManifestTypeSigDecl defn'
    AbstractTypeSigDecl k -> do
      checkKind k
      return $ AbstractTypeSigDecl k
    AliasTypeSigDecl alias -> do
      (alias', _) <- checkTypeAlias alias
      return $ AliasTypeSigDecl alias'

