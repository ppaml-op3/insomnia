{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses
  #-}
module Insomnia.ModelType where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr (Expr)
import Insomnia.TypeDefn

import Insomnia.Common.Stochasticity

data ModelType =
  SigMT !Signature -- "{ decls ... }"
  | IdentMT !SigIdentifier -- "X_SIG"
  deriving (Show, Typeable, Generic)

data Signature =
  UnitSig
  | ValueSig Stochasticity Field Type Signature
  | TypeSig Field (Bind (TyConName, Embed TypeSigDecl) Signature)
  | SubmodelSig Field (Bind (Identifier, Embed ModelType) Signature)
    deriving (Show, Typeable, Generic)

-- | A type declaration in a signature.
-- This should really be @Either Kind TypeDefn@ or perhaps
-- @Either Kind (Kind, TypeDefn)@, but we will separate them, for now.
-- The invariant, however, is that both Maybes can't be Nothing.
data TypeSigDecl =
  AbstractTypeSigDecl !Kind
  | ManifestTypeSigDecl !TypeDefn
  | AliasTypeSigDecl !TypeAlias
  deriving (Show, Typeable, Generic)

instance Alpha ModelType
instance Alpha Signature
instance Alpha TypeSigDecl

instance Subst Path Signature
instance Subst Path TypeSigDecl
instance Subst Path ModelType

instance Subst ValueConstructor ModelType
instance Subst ValueConstructor Signature
instance Subst ValueConstructor TypeSigDecl

instance Subst TypeConstructor ModelType
instance Subst TypeConstructor Signature
instance Subst TypeConstructor TypeSigDecl

-- model types do not have expressions in them.
instance Subst Expr ModelType where
  subst _ _ = id
  substs _ = id
