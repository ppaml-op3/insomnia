{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Typecheck "module type" and "module type" expressions.
module Insomnia.Typecheck.ModuleType where

import qualified Unbound.Generics.LocallyNameless as U

import Control.Applicative ((<$>))

import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Field, Path(..))
import Insomnia.Types (TypeConstructor(..), Kind(..))
import Insomnia.ModuleType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, checkTypeAlias)
import Insomnia.Typecheck.ExtendModuleCtx (extendTypeSigDeclCtx, extendModuleCtx)
import Insomnia.Typecheck.Selfify (selfifySignature)

-- | Check that the given module type expression is well-formed, and
-- return both the module type expression and the signature that it
-- "evaluates" to.
checkModuleType :: ModuleType -> TC (ModuleType, SigV Signature)
checkModuleType (SigMT sigv) = do
  sigv' <- checkSigV Nothing sigv
  return (SigMT sigv', sigv')
checkModuleType (IdentMT ident) = do
  sigv <- lookupModuleType ident
  return (IdentMT ident, sigv)

checkSigV :: Maybe Path -> SigV Signature -> TC (SigV Signature)
checkSigV mpath (SigV msig modK) = flip SigV modK <$> checkSignature mpath modK msig

checkSignature :: Maybe Path -> ModuleKind -> Signature -> TC Signature
checkSignature mpath_ _modK = flip (checkSignature' mpath_) ensureNoDuplicateFields
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
      U.lunbind bnd $ \((tycon, U.unembed -> tsd), sig) -> do
        let dcon = TCLocal tycon
        -- guardDuplicateDConDecl dcon -- can't happen
        tsd' <- checkTypeSigDecl dcon tsd
        extendTypeSigDeclCtx dcon tsd
          $ checkSignature' mpath sig $ \(sig', flds) ->
           kont (TypeSig fld $ U.bind (tycon, U.embed tsd') sig', fld:flds)
    checkSignature' mpath (SubmoduleSig fld bnd) kont =
      U.lunbind bnd $ \((modIdent, U.unembed -> modTy), sig) -> do
        let modPath = mpathAppend mpath fld
        (modTy', modSigV) <- checkModuleType modTy
        let sig' = U.subst modIdent modPath sig
        case modSigV of
         (SigV modSig ModuleMK) -> do
           selfSig <- selfifySignature modPath modSig
           extendModuleCtx selfSig
             $ checkSignature' mpath sig'
             $ \(sig'', flds) ->
                kont (SubmoduleSig fld $ U.bind (modIdent, U.embed modTy') sig'', fld:flds)
         (SigV _modSig ModelMK) -> do
           -- N.B. We don't add modSig to the environment because in
           -- fact there's nothing that can be done with it in a
           -- signature!  you can't project out of a model, so its
           -- type components aren't useful, and you can't sample the
           -- submodel in the signature because sampling only happens
           -- in modules, not module types!
           checkSignature' mpath sig'
           $ \(sig'', flds) ->
              kont (SubmoduleSig fld $ U.bind (modIdent, U.embed modTy') sig'', fld:flds)

mpathAppend :: Maybe Path -> Field -> Path
mpathAppend Nothing fld = IdP (U.s2n fld)
mpathAppend (Just p) fld = ProjP p fld

checkTypeSigDecl :: TypeConstructor -> TypeSigDecl -> TC TypeSigDecl
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

