{-# LANGUAGE
      MultiParamTypeClasses, 
      ViewPatterns,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.Model where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Types
import Insomnia.TypeDefn

import Insomnia.Expr (Var, Expr)

data ModelExpr =
  ModelStruct Model
  deriving (Show)

-- A single model.
data Model = Model { modelDecls :: [Decl] }
              deriving (Show)

-- | A declaration
data Decl =
  ValueDecl !ValueDecl -- ^ declaration of a value
  | TypeDefn !TypeDefn   -- ^ generative construction of new types
  deriving (Show)

data ValueDecl =
  FunDecl !Var !Expr     -- ^ function definition "fun f x = ..."
  | ValDecl !Var !Expr   -- ^ a value definition "val x = ..."
  | SampleDecl !Var !Expr -- ^ a sampled value definition "val x ~ ..."
  | SigDecl !Var !Type   -- ^ a function signature "sig f :: A -> B"
  deriving (Show)
