{-# LANGUAGE FlexibleContexts #-}
module Insomnia.Typecheck.ExtendModuleCtx (
  extendTypeSigDeclCtx
  , extendModuleCtxV
  , extendModuleCtx
  ) where

import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Insomnia.Types (TypeConstructor(..))
import Insomnia.Common.ModuleKind
import Insomnia.ModuleType (TypeSigDecl(..), SigV(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.SelfSig (SelfSig(..))
import Insomnia.Typecheck.TypeDefn (extendTypeDefnCtx, extendTypeAliasCtx)

extendTypeSigDeclCtx :: TypeConstructor -> TypeSigDecl -> TC a -> TC a
extendTypeSigDeclCtx dcon tsd = do
  case tsd of
    ManifestTypeSigDecl defn -> extendTypeDefnCtx dcon defn
    AbstractTypeSigDecl k ->
      extendDConCtx dcon (GenerativeTyCon $ AbstractType k)
    AliasTypeSigDecl alias -> extendTypeAliasCtx dcon alias
  
extendModuleCtxV :: SigV SelfSig -> TC a -> TC a
extendModuleCtxV (SigV sig mk) =
  case mk of
   -- can't address model components directly.
   ModelMK -> id
   ModuleMK -> extendModuleCtx sig

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
extendModuleCtx (SubmoduleSelfSig _path subSigV msig) =
  extendModuleCtxV subSigV
  . extendModuleCtx msig
