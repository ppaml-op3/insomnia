{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, TemplateHaskell,
      MultiParamTypeClasses
  #-}
module Insomnia.ModelType where

import Control.Lens
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn

data ModelType =
  SigMT !Signature -- "{ decls ... }"
  | IdentMT !Identifier -- "X_SIG"
  deriving (Show, Typeable, Generic)

data Signature =
  UnitSig
  | ValueSig Field Type Signature
  | TypeSig Field (Bind (Identifier, Embed TypeSigDecl) Signature)
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

instance Subst Path Signature
instance Subst Path TypeSigDecl
