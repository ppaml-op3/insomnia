{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Typecheck "module type" and "module type" expressions.
module Insomnia.Typecheck.ModuleType where

import qualified Unbound.Generics.LocallyNameless as U

import Control.Lens
import Control.Applicative ((<$>))
import Control.Monad (unless)
import Data.Monoid ((<>))

import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Identifier (Field, Path(..))
import Insomnia.Types (TypeConstructor(..), Kind(..))
import Insomnia.ModuleType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, checkTypeAlias)
import Insomnia.Typecheck.ExtendModuleCtx (extendTypeSigDeclCtx, extendModuleCtxV)
import Insomnia.Typecheck.Selfify (selfifySigV)

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

-- | Returns True iff a value signature with the given stochasticity
-- appears in a module type with the given type.  Random variables are
-- illegal in modules.  All other combos okay.
compatibleModuleStochasticity :: ModuleKind -> Stochasticity -> Bool
compatibleModuleStochasticity ModuleMK RandomVariable = False
compatibleModuleStochasticity _ _ = True

-- | @compatibleSubmodule mod1 mod2@ returns True iff a submodule of
-- kind @mod2@ can appear inside a @mod1@.  Models may not appear
-- inside models.  All other combos okay.
compatibleSubmodule :: ModuleKind -> ModuleKind -> Bool
compatibleSubmodule ModelMK ModelMK = False
compatibleSubmodule _ _ = True

checkSigV :: Maybe Path -> SigV Signature -> TC (SigV Signature)
checkSigV mpath (SigV msig modK) = flip SigV modK <$> checkSignature mpath modK msig

checkSignature :: Maybe Path -> ModuleKind -> Signature -> TC Signature
checkSignature mpath_ modK = flip (checkSignature' mpath_) ensureNoDuplicateFields
  where
    -- TODO: actually check that the field names are unique.
    ensureNoDuplicateFields :: (Signature, [Field]) -> TC Signature
    ensureNoDuplicateFields (sig, _flds) = return sig

    checkSignature' :: Maybe Path
                       -> Signature -> ((Signature, [Field]) -> TC Signature)
                       -> TC Signature
    checkSignature' _mpath UnitSig kont = kont (UnitSig, [])
    checkSignature' mpath (ValueSig stoch fld ty sig) kont = do
        ty' <- checkType ty KType
        unless (compatibleModuleStochasticity modK stoch) $ do
          typeError (formatErr modK <> " signature may not contain a "
                     <> formatErr stoch <> " variable " <> formatErr fld)
        checkSignature' mpath sig $ \(sig', flds) ->
          kont (ValueSig stoch fld ty' sig', fld:flds)
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
        unless (compatibleSubmodule modK (modSigV^.sigVKind)) $ do
          typeError (formatErr modK <> " signature may not contain a sub-"
                     <> formatErr (modSigV^.sigVKind) <> " " <> formatErr modPath)
        selfSigV <- selfifySigV modPath modSigV
        let sig' = U.subst modIdent modPath sig
        extendModuleCtxV selfSigV
          $ checkSignature' mpath sig' $ \(sig'', flds) ->
          kont (SubmoduleSig fld $ U.bind (modIdent, U.embed modTy') sig''
                , fld:flds)
        

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

