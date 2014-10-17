{-# LANGUAGE DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.ModelType where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.Expr (Var)

data ModelType =
  SigMT !Signature
  deriving (Show, Typeable, Generic)

data Signature =
  UnitSig
  | ValueSig Field (Bind (Var, Embed Type) Signature)
  | TypeSig Field (Bind (TyVar, Embed TypeSigDecl) Signature)
    deriving (Show, Typeable, Generic)

data TypeSigDecl =
  TypeSigDecl { _typeSigDeclKind :: Kind
              , _typeSigDeclManifest :: Maybe TypeDefn
              }
  deriving (Show, Typeable, Generic)

instance Alpha ModelType
instance Alpha Signature
instance Alpha TypeSigDecl

