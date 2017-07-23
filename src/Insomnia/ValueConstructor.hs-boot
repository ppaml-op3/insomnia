{-# LANGUAGE MultiParamTypeClasses,CPP #-}
module Insomnia.ValueConstructor where

#if MIN_VERSION_base(4,7,0)
#else
import Data.Typeable (Typeable)
#endif
import Unbound.Generics.LocallyNameless (Alpha)

data ValueConstructor

data ConstructorDef

instance Show ConstructorDef
#if MIN_VERSION_base(4,7,0)
#else
instance Typeable ConstructorDef
#endif
instance Alpha ConstructorDef

instance Show ValueConstructor
#if MIN_VERSION_base(4,7,0)
#else
instance Typeable ValueConstructor
#endif
instance Alpha ValueConstructor
