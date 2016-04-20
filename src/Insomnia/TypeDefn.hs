{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses
  #-}
module Insomnia.TypeDefn where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types (Type, TypePath,
                       TypeConstructor,
                       Nat, KindedTVar)
import Insomnia.ValueConstructor (ValueConstructor, ConstructorDef)

-- | A type alias does not define a new type, but it defines a new name for
-- an existing type expression.  If it's actually a data type or enum
-- type copy, we also bring along their definition (so that we can
-- bring the constructors into scope)
data TypeAlias =
  ManifestTypeAlias !(Bind [KindedTVar] Type) -- type T = P.S
  | DataCopyTypeAlias !TypePath !TypeDefn     -- datatype T = datatype P.S
               deriving (Show, Typeable, Generic)

-- | A declaration of a type.  Note that we omit providing the name
-- of the type here. It will be provided by the model that the definition
-- is a part of.
data TypeDefn =
    -- | "data T (a::K)... = C1 T11 ... T1m | C2 | C3 T31 ... T3n"
  DataDefn !DataDefn
  | EnumDefn !Nat
  deriving (Show, Typeable, Generic)

-- | a DataDefn of kind k1 -> ... -> kN -> * with the given construtors.
type DataDefn = Bind [KindedTVar] [ConstructorDef]

-- | This type exists merely so that we can give it a Pretty instance
-- in the pretty printer.
data PrettyField a = PrettyField !Field !a

type PrettyTypeDefn = PrettyField TypeDefn
type PrettyTypeAlias = PrettyField TypeAlias

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha TypeDefn
instance Alpha TypeAlias

instance Subst SigPath TypeAlias
instance Subst SigPath TypeDefn

instance Subst Path TypeDefn
instance Subst Path TypeAlias


-- -- Capture avoid substitution of types for type variables in the following.
instance Subst Type TypeAlias
instance Subst Type TypeDefn

instance Subst ValueConstructor TypeAlias where
  subst _ _ = id
  substs _ = id

instance Subst ValueConstructor TypeDefn

instance Subst TypeConstructor TypeAlias
instance Subst TypeConstructor TypeDefn


