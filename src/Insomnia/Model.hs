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
import Insomnia.ModuleType

import Insomnia.Common.Stochasticity
import Insomnia.Expr (Expr)

data ModelExpr =
  ModelStruct !Model -- model specified here
  | ModelSeal !ModelExpr !ModuleType -- generative sealing
  | ModelAssume !ModuleType    -- model assumed to exist.
  | ModelId !Path       -- previously named model
  deriving (Show, Typeable, Generic)

-- A single model.
data Model = Model { modelDecls :: [Decl] }
              deriving (Show, Typeable, Generic)

-- | A declaration
data Decl =
  ValueDecl !Field !ValueDecl -- ^ declaration of a value
  | TypeDefn !Field !TypeDefn   -- ^ generative construction of new types
  | TypeAliasDefn !Field !TypeAlias -- ^ a type alias definition
  | SubmodelDefn !Field !ModelExpr -- ^ a nested module definition
  deriving (Show, Typeable, Generic)

data ValueDecl =
  FunDecl !Expr     -- ^ function definition "fun f x = ..."
  | ParameterDecl !Expr -- ^ parameter definition "parameter x = ... "
  | ValDecl !Expr   -- ^ a value definition "val x = ..." (sugar for "val x ~ = ireturn ...")
  | SampleDecl !Expr -- ^ a sampled value definition "val x ~ ..."
  | SigDecl !Stochasticity !Type   -- ^ a function signature "[parameter] sig f :: A -> B"
  deriving (Show, Typeable, Generic)

instance Alpha ModelExpr
instance Alpha Model
instance Alpha Decl
instance Alpha ValueDecl

instance Subst Path ModelExpr
instance Subst Path Model
instance Subst Path Decl
instance Subst Path ValueDecl

instance Subst TypeConstructor ModelExpr
instance Subst TypeConstructor Model
instance Subst TypeConstructor Decl
instance Subst TypeConstructor ValueDecl

instance Subst ValueConstructor ModelExpr
instance Subst ValueConstructor Model
instance Subst ValueConstructor Decl
instance Subst ValueConstructor ValueDecl

instance Subst Expr ModelExpr
instance Subst Expr Model
instance Subst Expr Decl
instance Subst Expr ValueDecl
