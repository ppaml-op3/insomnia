{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses
  #-}
module Insomnia.TypeDefn where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Types

-- | A declaration of a type
data TypeDefn =
    -- | "data T (a::K)... = C1 T11 ... T1m | C2 | C3 T31 ... T3n"
  DataDefn !Con !DataDefn
  | EnumDefn !Con !Nat
  deriving (Show, Typeable, Generic)

-- a DataDefn of kind k1 -> ... -> kN -> * with the given construtors.
type DataDefn = Bind [KindedTVar] [ConstructorDef]

data ConstructorDef = ConstructorDef !Con [Type]
                    deriving (Show, Typeable, Generic)

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha ConstructorDef
instance Alpha TypeDefn

-- Capture avoid substitution of types for type variables in the following.
instance Subst Type ConstructorDef

