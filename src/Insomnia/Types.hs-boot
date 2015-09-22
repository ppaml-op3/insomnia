{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.Types where

import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Control.Lens (Traversal)

import Unbound.Generics.LocallyNameless (Name, Alpha, Subst)

import Insomnia.Identifier (Path)

data Kind
data Type
data TypeConstructor
data TypePath
data Label

instance Show Kind
instance Show Type
instance Show TypePath

instance Generic Type
instance Typeable Type

instance Alpha Kind
instance Alpha Type
instance Alpha TypeConstructor
instance Alpha TypePath


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