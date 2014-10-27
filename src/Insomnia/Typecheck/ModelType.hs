{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Typecheck "model type" expressions.
module Insomnia.Typecheck.ModelType where

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier (Field, Path(..))
import Insomnia.Types (Con(..), Kind(..))
import Insomnia.ModelType

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkKind, checkType)
import Insomnia.Typecheck.TypeDefn (checkTypeDefn, extendTypeDefnCtx)

extendTypeSigDeclCtx :: Con -> TypeSigDecl -> TC a -> TC a
extendTypeSigDeclCtx dcon tsd = do
  case tsd of
    TypeSigDecl _ (Just defn) -> extendTypeDefnCtx dcon defn
    TypeSigDecl (Just k) Nothing -> extendDConCtx dcon (AbstractType k)
    TypeSigDecl _ _ -> error "unexpected TypeSigDecl in extendTypeSigDeclCtx"

-- | Check that the given model type expression is well-formed, and
-- return both the model type expression and the signature that it
-- "evaluates" to.
checkModelType :: ModelType -> TC (ModelType, Signature)
checkModelType (SigMT msig) = do
  msig' <- checkSignature msig
  return (SigMT msig', msig')
checkModelType (IdentMT ident) = do
  msig <- lookupModelType ident
  return (IdentMT ident, msig)

checkSignature :: Signature -> TC Signature
checkSignature = flip checkSignature' ensureNoDuplicateFields
  where
    -- TODO: actually check that the field names are unique.
    ensureNoDuplicateFields :: (Signature, [Field]) -> TC Signature
    ensureNoDuplicateFields (sig, _flds) = return sig
    checkSignature' :: Signature -> ((Signature, [Field]) -> TC Signature)
                       -> TC Signature
    checkSignature' UnitSig kont = kont (UnitSig, [])
    checkSignature' (ValueSig fld ty sig) kont = do
        ty' <- checkType ty KType
        checkSignature' sig $ \(sig', flds) ->
          kont (ValueSig fld ty' sig', fld:flds)
    checkSignature' (TypeSig fld bnd) kont =
      U.lunbind bnd $ \((tyident, U.unembed -> tsd), sig) -> do
        let dcon = Con (IdP tyident)
        -- guardDuplicateDConDecl dcon -- can't happen
        tsd' <- checkTypeSigDecl dcon tsd
        extendTypeSigDeclCtx dcon tsd
          $ checkSignature' sig $ \(sig', flds) ->
           kont (TypeSig fld $ U.bind (tyident, U.embed tsd') sig', fld:flds)

checkTypeSigDecl :: Con -> TypeSigDecl -> TC TypeSigDecl
checkTypeSigDecl dcon tsd =
  case tsd of
    TypeSigDecl Nothing (Just defn) -> do
      (defn', _) <-  checkTypeDefn dcon defn
      return $ TypeSigDecl Nothing (Just defn')
    TypeSigDecl (Just k) Nothing -> do
      checkKind k
      return $ TypeSigDecl (Just k) Nothing
    TypeSigDecl Nothing Nothing ->
      typeError "checkTypeSigDecl: Nothing Nothing - internal error"
    TypeSigDecl (Just _) (Just _) ->
      -- TODO: what do we think of this? Just keep the definition
      typeError "checkTypeSigDecl: Just Just - internal error, perhaps."
