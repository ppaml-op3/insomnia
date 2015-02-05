{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}
module FOmega.Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import {-# SOURCE #-} FOmega.Pretty (ppType, ppTerm, ppKind)
import Insomnia.Pretty (Pretty(..))

-- | There will be some stylized records that have predefined field
-- names distinct from what a user may write.
data Field =
  FVal
  | FType
  | FSig
  -- data type definition field
  | FData
  -- data type constructor field
  | FCon !String
  -- user defined record fields
  | FUser !String
    deriving (Show, Eq, Ord, Typeable, Generic)

data Kind =
  KType
  | KArr !Kind !Kind
    deriving (Show, Eq, Typeable, Generic)

type TyVar = Name Type

-- TODO: Maybe use a (βη)-normalized representation?
data Type =
  TV !TyVar
  | TLam !(Bind (TyVar, Embed Kind) Type)
  | TApp !Type !Type
  | TForall !(Bind (TyVar, Embed Kind) Type)
  | TExist !ExistPack
  | TRecord ![(Field, Type)]
  | TArr !Type !Type
  deriving (Show, Typeable, Generic)

type ExistPack = Bind (TyVar, Embed Kind) Type

type Var = Name Term

data Term =
  V !Var
  | Lam !(Bind (Var, Embed Type) Term)
  | App !Term !Term
  | PLam !(Bind (TyVar, Embed Kind) Term)
  | PApp !Term !Type
  | Record ![(Field, Term)]
  | Proj !Term !Field
  | Pack !Type !Term !ExistPack
  | Unpack !(Bind (TyVar, Var, Embed Term) Term)
  deriving (Show, Typeable, Generic)

-- * Alpha equivalence and Substitution


instance Alpha Field
instance Alpha Kind
instance Alpha Type
instance Alpha Term

instance Subst Type Type where
  isvar (TV a) = Just (SubstName a)
  isvar _ = Nothing

-- no types inside kinds
instance Subst Type Kind where
  subst _ _ = id
  substs _ = id
instance Subst Type Field where
  subst _ _ = id
  substs _ = id

instance Subst Term Term where
  isvar (V a) = Just (SubstName a)
  isvar _ = Nothing

instance Subst Term Type where
  subst _ _ = id
  substs _ = id

instance Subst Term Field where
  subst _ _ = id
  substs _ = id

instance Subst Term Kind where
  subst _ _ = id
  substs _ = id

-- * Pretty printing

instance Pretty Kind where pp = ppKind
instance Pretty Type where pp = ppType
instance Pretty Term where pp = ppTerm

-- * Utilities

kArrs :: [Kind] -> Kind -> Kind
kArrs [] = id
kArrs (k:ks) = KArr k . kArrs ks

tForalls :: [(TyVar, Kind)] -> Type -> Type
tForalls [] = id
tForalls ((tv,k):tvks) =
  TForall . bind (tv, embed k) . tForalls tvks

tApps :: Type -> [Type] -> Type
tApps = flip tApps'
  where
    tApps' [] = id
    tApps' (t:ts) = tApps' ts . (`TApp` t)

tArrs :: [Type] -> Type -> Type
tArrs [] = id
tArrs (t:ts) = (t `TArr`) . tArrs ts
