{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.Module where

import Unbound.Generics.LocallyNameless (Alpha, Subst)

import Insomnia.Identifier (Path)
import {-# SOURCE #-} Insomnia.Types (Type, TypeConstructor)
import Insomnia.TypeDefn (ValueConstructor)

data ModuleExpr

instance Show ModuleExpr
instance Alpha ModuleExpr

instance Subst Path ModuleExpr
instance Subst Type ModuleExpr

instance Subst TypeConstructor ModuleExpr
instance Subst ValueConstructor ModuleExpr