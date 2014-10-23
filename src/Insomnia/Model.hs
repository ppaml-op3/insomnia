{-# LANGUAGE
      MultiParamTypeClasses, 
      ViewPatterns,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.Model where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModelType

import Insomnia.Expr (Expr)

data ModelExpr =
  ModelStruct !Model -- model specified here
  | ModelAscribe !ModelExpr !ModelType -- transluscent ascription
  | ModelAssume !ModelType    -- model assumed to exist.
  deriving (Show)

-- A single model.
data Model = Model { modelDecls :: [Decl] }
              deriving (Show)

-- | A declaration
data Decl =
  ValueDecl !Field !ValueDecl -- ^ declaration of a value
  | TypeDefn !Field !TypeDefn   -- ^ generative construction of new types
  deriving (Show, Typeable, Generic)

data ValueDecl =
  FunDecl !Expr     -- ^ function definition "fun f x = ..."
  | ValDecl !Expr   -- ^ a value definition "val x = ..."
  | SampleDecl !Expr -- ^ a sampled value definition "val x ~ ..."
  | SigDecl !Type   -- ^ a function signature "sig f :: A -> B"
  deriving (Show, Typeable, Generic)

instance Alpha Decl
instance Alpha ValueDecl

instance Subst Path Decl
instance Subst Path ValueDecl

instance Subst Expr Decl
instance Subst Expr ValueDecl

