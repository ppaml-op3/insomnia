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

import Insomnia.Expr (Var, Expr)

-- A single model.
data Model = Model { modelDecls :: [Decl] }
              deriving (Show)

-- | A declaration
data Decl =
  ValueDecl !ValueDecl -- ^ declaration of a value
  | TypeDecl !TypeDecl   -- ^ generative construction of new types
  deriving (Show)

-- | A declaration of a type
data TypeDecl =
    -- | "data T (a::K)... = C1 T11 ... T1m | C2 | C3 T31 ... T3n"
  DataDecl !Con !DataDecl
  | EnumDecl !Con !Nat
  deriving (Show)

data ValueDecl =
  FunDecl !Var !Expr     -- ^ function definition "fun f x = ..."
  | ValDecl !Var !Expr   -- ^ a value definition "val x = ..."
  | SampleDecl !Var !Expr -- ^ a sampled value definition "val x ~ ..."
  | SigDecl !Var !Type   -- ^ a function signature "sig f :: A -> B"
  deriving (Show)

-- a DataDecl of kind k1 -> ... -> kN -> * with the given construtors.
type DataDecl = Bind [KindedTVar] [ConstructorDef]

data ConstructorDef = ConstructorDef !Con [Type]
                    deriving (Show, Typeable, Generic)

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha ConstructorDef

-- Capture avoid substitution of types for type variables in the following.
instance Subst Type ConstructorDef

