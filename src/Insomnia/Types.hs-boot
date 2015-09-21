{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.Types where

import Control.Lens (Traversal)

import Unbound.Generics.LocallyNameless (Alpha, Subst)

import Insomnia.Identifier (Path)

data Type
data TypeConstructor

instance Alpha Type
instance Alpha TypeConstructor

instance Subst Path Type
instance Subst Path TypeConstructor

data TypePath

class TraverseTypes s t where
  traverseTypes :: Traversal s t Type Type