{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, FlexibleInstances #-}
module Insomnia.Common.ModuleKind where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

data ModuleKind = ModuleMK | ModelMK
                deriving (Show, Eq, Typeable, Generic)

instance Alpha ModuleKind

instance Subst a ModuleKind where
  subst _ _ = id
  substs _ = id
