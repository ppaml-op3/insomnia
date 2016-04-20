{-# LANGUAGE MultiParamTypeClasses, DeriveDataTypeable, DeriveGeneric, TemplateHaskell #-}
module Insomnia.ValueConstructor (ValConPath(..),
                                  ValConName,
                                  ValueConstructor(..),
                                  InferredValConPath(..),
                                  ConstructorDef(..),
                                  constructorDefTypes,
                                  canonicalizeConstructorDefs) where
import Control.Lens
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless (Name, Alpha(..), Subst(..), SubstName(..))
import Insomnia.Identifier (Field, Path, SigPath)
import Insomnia.Types (Kind, Label, Type, TypePath, TypeConstructor)
import Insomnia.Common.Literal (Literal)


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


instance Alpha ValConPath
instance Alpha InferredValConPath
instance Alpha ValueConstructor
instance Alpha ConstructorDef

instance Subst Path ValConPath
instance Subst Path InferredValConPath
instance Subst Path ValueConstructor
instance Subst Path ConstructorDef

instance Subst SigPath ConstructorDef


instance Subst Type ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst Type ValueConstructor where
  subst _ _ = id
  substs _ = id
instance Subst Type ConstructorDef

instance Subst TypeConstructor ConstructorDef

instance Subst ValueConstructor ConstructorDef

instance Subst ValueConstructor ValueConstructor where
  isvar (VCLocal c) = Just (SubstName c)
  isvar _ = Nothing

instance Subst ValueConstructor ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor InferredValConPath where
  subst _ _ = id
  substs _ = id

instance Subst TypeConstructor ValConPath where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor ValueConstructor where
  subst _ _ = id
  substs _ = id


instance Subst ValueConstructor Path where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor SigPath where
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

instance Subst ValueConstructor TypePath where
  subst _ _ = id
  substs _ = id

instance Subst ValueConstructor Type where
  subst _ _ = id
  substs _ = id

