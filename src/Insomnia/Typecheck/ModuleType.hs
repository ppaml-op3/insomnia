{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Typecheck "module type" and "module type" expressions.
module Insomnia.Typecheck.ModuleType where

import Control.Applicative ((<$>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier (Field, Path(..))
import Insomnia.Types (TypeConstructor(..), Kind(..))
import Insomnia.ModuleType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, checkTypeAlias)
import Insomnia.Typecheck.ExtendModuleCtx (extendTypeSigDeclCtx, extendModuleCtxNF)
import Insomnia.Typecheck.WhnfModuleType (reduceWhereModuleTypeNF)

-- | Check that the given module type expression is well-formed, and
-- return both the module type expression and the signature that it
-- "evaluates" to.
checkModuleType :: ModuleType -> TC (ModuleType, ModuleTypeNF)
checkModuleType (SigMT sigv) = do
  sigv' <- checkSigV Nothing sigv
  return (SigMT sigv', SigMTNF sigv')
checkModuleType (FunMT bnd) =
  U.lunbind bnd $ \(args, body) ->
  extendModuleCtxFunctorArgs args $ \args' argsnf -> do
    (body', bodynf) <- checkModuleType body
    return (FunMT $ U.bind args' body',
            FunMTNF $ U.bind argsnf bodynf)
checkModuleType (IdentMT ident) = do
  mtnf <- lookupModuleType ident
  return (IdentMT ident, mtnf)
checkModuleType (WhereMT mt whClause) = do
  (mt', mtnf) <- checkModuleType mt
  mtnf' <- reduceWhereModuleTypeNF mtnf whClause
  return (WhereMT mt' whClause, mtnf')

-- | Given a telescope of functor arguments (id : Mt1, ..., id : Mtn)
-- extend the context of the continuation with the corresponding
-- identifiers.
extendModuleCtxFunctorArgs :: Telescope (FunctorArgument ModuleType)
                    -> (Telescope (FunctorArgument ModuleType)
                        -> Telescope (FunctorArgument ModuleTypeNF)
                        -> TC a)
                    -> TC a
extendModuleCtxFunctorArgs tele kont =
  case tele of
   NilT -> kont NilT NilT
   ConsT (U.unrebind -> (arg, tele')) ->
     extendModuleCtxFunctorArg arg $ \arg' argNF ->
     extendModuleCtxFunctorArgs tele' $ \tele'' teleNF ->
     kont (ConsT $ U.rebind arg' tele'') (ConsT $ U.rebind argNF teleNF)
  
extendModuleCtxFunctorArg :: FunctorArgument ModuleType
                          -> (FunctorArgument ModuleType
                              -> FunctorArgument ModuleTypeNF
                              -> TC a)
                          -> TC a
extendModuleCtxFunctorArg (FunctorArgument ident modK (U.unembed -> modTy)) kont = do
  (modTy', nf) <- checkModuleType modTy
  extendModuleCtxNF (IdP ident) nf
    $ kont (FunctorArgument ident modK (U.embed modTy')) (FunctorArgument ident modK (U.embed nf))

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
        (modTy', modSigNF) <- checkModuleType modTy
        let sig' = U.subst modIdent modPath sig
        extendModuleCtxNF modPath modSigNF
          $ checkSignature' mpath sig'
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

