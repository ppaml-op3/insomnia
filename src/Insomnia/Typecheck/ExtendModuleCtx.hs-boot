module Insomnia.Typecheck.ExtendModuleCtx where

import Insomnia.Identifier (Path)
import Insomnia.ModuleType (ModuleTypeNF, TypeSigDecl)
import Insomnia.Types (TypeConstructor)

import Insomnia.Typecheck.Env (TC)
import Insomnia.Typecheck.SelfSig (SelfSig)

extendTypeSigDeclCtx :: TypeConstructor -> TypeSigDecl -> TC a -> TC a
extendModuleCtxNF :: Path -> ModuleTypeNF -> TC a -> TC a
extendModuleCtx :: SelfSig -> TC a -> TC a
