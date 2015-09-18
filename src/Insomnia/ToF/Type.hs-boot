module Insomnia.ToF.Type where

import Insomnia.Types (Kind, Type, KindedTVar)
import Insomnia.TypeDefn (TypeAlias)

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F
import Insomnia.ToF.Env (ToF)

withTyVars :: ToF m => [KindedTVar] -> ([(F.TyVar, F.Kind)] -> m r) -> m r

kind :: Monad m => Kind -> m F.Kind
type' :: ToF m => Type -> m (F.Type, F.Kind)
typeAlias :: ToF m => TypeAlias -> m F.SemanticSig
