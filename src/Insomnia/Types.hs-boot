{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.Types where

import Unbound.Generics.LocallyNameless (Alpha, Subst)

import Insomnia.Identifier (Path)

data Type
data TypeConstructor

instance Alpha Type
instance Alpha TypeConstructor

instance Subst Path Type
instance Subst Path TypeConstructor

data TypePath