{-# LANGUAGE MultiParamTypeClasses #-}
module Insomnia.ValueConstructor where

import Data.Typeable (Typeable)
import Unbound.Generics.LocallyNameless (Alpha)

data ValueConstructor

data ConstructorDef

instance Show ConstructorDef
instance Typeable ConstructorDef
instance Alpha ConstructorDef

instance Show ValueConstructor
instance Typeable ValueConstructor
instance Alpha ValueConstructor
