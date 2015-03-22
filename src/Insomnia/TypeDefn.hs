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
import Insomnia.Common.Literal (Literal)

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

-- | A ValConName stands for a value constructor.  Unlike a normal
-- value-level variable, it may only be substituted for by a path to a
-- value constructor, rather than an arbitrary expression.
type ValConName = Name ValueConstructor

-- | A ValConPath picks out a value constructor field in the model
-- associated with the given path.
data ValConPath = ValConPath !Path !Field
                deriving (Show, Eq, Ord, Typeable, Generic)

data InferredValConPath = InferredValConPath !TypePath !Field
                        deriving (Show, Typeable, Generic)

-- | Value constructors may be either local to the current model, or
-- specified along a global path.  (This datatype is here, rather
-- than in Insomnia.Expr because while type definitions don't talk
-- about value constructors, they do mention ValConName, which is a
-- mere type alias for a 'Name ValueConstructor'.)
data ValueConstructor =
  VCLocal !ValConName
   -- before typechecking, a path to the constructor;
   -- after typechecking, a path to the type and the name of the construtor
  | VCGlobal !(Either ValConPath InferredValConPath)
  deriving (Show, Typeable, Generic)

-- | A value constructor with the given name, taking arguments of
-- the given types.
data ConstructorDef = ConstructorDef {
  _constructorDefCon :: !ValConName
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
instance Alpha ValConPath
instance Alpha InferredValConPath
instance Alpha ValueConstructor

instance Subst Path TypeDefn
instance Subst Path ConstructorDef
instance Subst Path TypeAlias
instance Subst Path ValConPath
instance Subst Path InferredValConPath
instance Subst Path ValueConstructor

-- Capture avoid substitution of types for type variables in the following.
instance Subst Type ConstructorDef
instance Subst Type TypeAlias

instance Subst Type ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst Type ValueConstructor where
  subst _ _ = id
  substs _ = id

instance Subst ValueConstructor ValueConstructor where
  isvar (VCLocal c) = Just (SubstName c)
  isvar _ = Nothing

instance Subst ValueConstructor ConstructorDef
instance Subst ValueConstructor TypeDefn

instance Subst ValueConstructor ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor InferredValConPath where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor TypeAlias where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor Path where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor Kind where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor Label where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor Literal where
  subst _ _ = id
  substs _ = id

instance Subst ValueConstructor Type where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor TypePath where
  subst _ _ = id
  substs _ = id

instance Subst TypeConstructor ConstructorDef
instance Subst TypeConstructor TypeAlias
instance Subst TypeConstructor TypeDefn

instance Subst TypeConstructor ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor ValueConstructor where
  subst _ _ = id
  substs _ = id

