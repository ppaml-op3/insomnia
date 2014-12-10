module Insomnia.Typecheck.ExtendModuleCtx (
  extendTypeSigDeclCtx
  , extendModuleCtx
  ) where

import Control.Lens
import Control.Monad.Reader.Class (MonadReader(..))

import Insomnia.Types (TypeConstructor(..))
import Insomnia.ModuleType (TypeSigDecl(..))

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
  
-- | Given a (selfified) signature, add all of its fields to the context
-- by prefixing them with the given path - presumably the path of this
-- very module.
extendModuleCtx :: SelfSig -> TC a -> TC a
extendModuleCtx UnitSelfSig = id
extendModuleCtx (ValueSelfSig stoch qvar ty msig) =
  -- TODO: if we are moduleing joint distributions, does it ever make
  -- sense to talk about value components of other modules?
  local (envGlobals . at qvar ?~ (ty, stoch))
  . extendModuleCtx msig
extendModuleCtx (TypeSelfSig p tsd msig) =
  extendTypeSigDeclCtx (TCGlobal p) tsd
  . extendModuleCtx msig
extendModuleCtx (SubmoduleSelfSig _path subModSig _modK msig) =
  extendModuleCtx subModSig
  . extendModuleCtx msig
