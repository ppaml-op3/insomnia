{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, TemplateHaskell
  #-}
module Insomnia.ModelType where

import Control.Lens
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.Expr (Var)

data ModelType =
  SigMT !Signature -- "{ decls ... }"
  | IdentMT !Identifier -- "X_SIG"
  deriving (Show, Typeable, Generic)

data Signature =
  UnitSig
  | ValueSig Field (Bind (Var, Embed Type) Signature)
  | TypeSig Field (Bind (TyVar, Embed TypeSigDecl) Signature)
    deriving (Show, Typeable, Generic)

-- | A type declaration in a signature.
-- This should really be @Either Kind TypeDefn@ or perhaps
-- @Either Kind (Kind, TypeDefn)@, but we will separate them, for now.
-- The invariant, however, is that both Maybes can't be Nothing.
data TypeSigDecl =
  TypeSigDecl { _typeSigDeclKind :: Maybe Kind
              , _typeSigDeclManifest :: Maybe TypeDefn
              }
  deriving (Show, Typeable, Generic)

$(makeLenses ''TypeSigDecl)

instance Alpha ModelType
instance Alpha Signature
instance Alpha TypeSigDecl

