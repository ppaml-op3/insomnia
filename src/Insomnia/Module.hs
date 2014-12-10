{-# LANGUAGE
      MultiParamTypeClasses, 
      ViewPatterns,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.Module where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModuleType

import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Expr (Expr)

data ModuleExpr =
  ModuleStruct !Module !ModuleKind -- module specified here
  | ModuleSeal !ModuleExpr !ModuleType -- generative sealing
  | ModuleAssume !ModuleType    -- module assumed to exist.
  | ModuleId !Path       -- previously named module
  deriving (Show, Typeable, Generic)

-- A single module.
data Module = Module { moduleDecls :: [Decl] }
              deriving (Show, Typeable, Generic)

-- | A declaration
data Decl =
  ValueDecl !Field !ValueDecl -- ^ declaration of a value
  | TypeDefn !Field !TypeDefn   -- ^ generative construction of new types
  | TypeAliasDefn !Field !TypeAlias -- ^ a type alias definition
  | SubmoduleDefn !Field !ModuleExpr -- ^ a nested module definition
  deriving (Show, Typeable, Generic)

data ValueDecl =
  FunDecl !Expr     -- ^ function definition "fun f x = ..."
  | ParameterDecl !Expr -- ^ parameter definition "parameter x = ... "
  | ValDecl !Expr   -- ^ a value definition "val x = ..." (sugar for "val x ~ = ireturn ...")
  | SampleDecl !Expr -- ^ a sampled value definition "val x ~ ..."
  | SigDecl !Stochasticity !Type   -- ^ a function signature "[parameter] sig f :: A -> B"
  deriving (Show, Typeable, Generic)

instance Alpha ModuleExpr
instance Alpha Module
instance Alpha Decl
instance Alpha ValueDecl

instance Subst Path ModuleExpr
instance Subst Path Module
instance Subst Path Decl
instance Subst Path ValueDecl

instance Subst TypeConstructor ModuleExpr
instance Subst TypeConstructor Module
instance Subst TypeConstructor Decl
instance Subst TypeConstructor ValueDecl

instance Subst ValueConstructor ModuleExpr
instance Subst ValueConstructor Module
instance Subst ValueConstructor Decl
instance Subst ValueConstructor ValueDecl

instance Subst Expr ModuleExpr
instance Subst Expr Module
instance Subst Expr Decl
instance Subst Expr ValueDecl
