{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Insomnia.Typecheck.ExtendModuleCtx (
  extendTypeSigDeclCtx
  , extendModuleCtxNF
  , extendModuleCtx
  ) where

import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Insomnia.Identifier
import Insomnia.Types (TypeConstructor(..))
import Insomnia.Common.ModuleKind
import Insomnia.ModuleType (TypeSigDecl(..), ModuleTypeNF(..), SigV(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.Selfify (selfifySignature)
import Insomnia.Typecheck.TypeDefn (extendTypeDefnCtx, extendTypeAliasCtx)

extendTypeSigDeclCtx :: TypeConstructor -> TypeSigDecl -> TC a -> TC a
extendTypeSigDeclCtx dcon tsd = do
  case tsd of
    ManifestTypeSigDecl defn -> extendTypeDefnCtx dcon defn
    AbstractTypeSigDecl k ->
      extendDConCtx dcon (GenerativeTyCon $ AbstractType k)
    AliasTypeSigDecl alias -> extendTypeAliasCtx dcon alias

extendModuleCtxNF :: Path -> ModuleTypeNF -> TC a -> TC a
extendModuleCtxNF pmod mtnf =
  let
    extendModuleSig = case pmod of
      IdP modId -> extendModuleSigCtx modId mtnf
      _ -> id
    extendSelf = case mtnf of
      SigMTNF (SigV sig ModuleMK) -> \kont -> do
        selfSig <- selfifySignature pmod sig
        extendModuleCtx selfSig kont
      SigMTNF (SigV _ ModelMK) -> id
      FunMTNF {} -> id
  in
   extendModuleSig . extendSelf
   
-- | Given a (selfified) signature, add all of its fields to the context
-- by prefixing them with the given path - presumably the path of this
-- very module.
extendModuleCtx :: SelfSig -> TC a -> TC a
extendModuleCtx UnitSelfSig = id
extendModuleCtx (ValueSelfSig qvar ty msig) =
  local (envGlobals . at qvar ?~ ty)
  . extendModuleCtx msig
extendModuleCtx (TypeSelfSig p tsd msig) =
  extendTypeSigDeclCtx (TCGlobal p) tsd
  . extendModuleCtx msig
extendModuleCtx (SubmoduleSelfSig _path subSig msig) =
  extendModuleCtx subSig
  . extendModuleCtx msig
extendModuleCtx (GenerativeSelfSig _path _subSig msig) =
  extendModuleCtx msig
