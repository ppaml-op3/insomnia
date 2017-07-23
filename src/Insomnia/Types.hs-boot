{-# LANGUAGE MultiParamTypeClasses, CPP #-}
module Insomnia.Types where

#if MIN_VERSION_base(4,7,0)
#else
import Data.Typeable (Typeable)
#endif

import Control.Lens (Traversal)

import Unbound.Generics.LocallyNameless (Name, Alpha, Subst)

import Insomnia.Identifier (Path, SigPath)

data Kind
data Type
data TypeConstructor
data TypePath
data Label

instance Show Kind
instance Show Type
instance Show TypePath

#if MIN_VERSION_base(4,7,0)
#else
instance Typeable Type
#endif

instance Alpha Kind
instance Alpha Type
instance Alpha TypeConstructor
instance Alpha TypePath

instance Subst SigPath Kind
instance Subst SigPath Type
instance Subst SigPath TypePath


instance Subst Path Kind
instance Subst Path Type
instance Subst Path TypeConstructor
instance Subst Path TypePath

instance Subst Type Kind
instance Subst Type Type
instance Subst Type TypePath

instance Subst TypeConstructor Kind
instance Subst TypeConstructor Type
instance Subst TypeConstructor TypePath

type TyVar = Name Type

type KindedTVar = (TyVar, Kind)

type Nat = Integer

class TraverseTypes s t where
  traverseTypes :: Traversal s t Type Type
