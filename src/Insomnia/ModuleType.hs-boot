{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.ModuleType where

import Unbound.Generics.LocallyNameless (Alpha, Subst)

import Insomnia.Identifier (Path)
import {-# SOURCE #-} Insomnia.Types (Type, TypeConstructor, TraverseTypes)
import Insomnia.TypeDefn (ValueConstructor)

data ModuleType

instance Show ModuleType
instance Alpha ModuleType

instance Subst Path ModuleType
instance Subst Type ModuleType
instance Subst TypeConstructor ModuleType
instance Subst ValueConstructor ModuleType

instance TraverseTypes ModuleType ModuleType