{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses, TemplateHaskell
  #-}
module Insomnia.TypeDefn where

import Control.Lens
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types


-- | A type alias does not define a new type, but it defines a new name for
-- an existing type expression.
newtype TypeAlias = TypeAlias (Bind [KindedTVar] Type)
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

-- | A value constructor with the given name, taking arguments of
-- the given types.
data ConstructorDef = ConstructorDef {
  _constructorDefCon :: !Con
  , _constructorDefTypes :: [Type]
  }
                    deriving (Show, Typeable, Generic)

$(makeLenses ''ConstructorDef)

canonicalizeConstructorDefs :: [ConstructorDef] -> [ConstructorDef]
canonicalizeConstructorDefs = sortBy $ comparing $ view constructorDefCon

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha ConstructorDef
instance Alpha TypeDefn
instance Alpha TypeAlias

instance Subst Path TypeDefn
instance Subst Path ConstructorDef
instance Subst Path TypeAlias

-- Capture avoid substitution of types for type variables in the following.
instance Subst Type ConstructorDef
instance Subst Type TypeAlias

instance Subst TypeConstructor ConstructorDef
instance Subst TypeConstructor TypeAlias
instance Subst TypeConstructor TypeDefn
