-- | AST for a fragment of Racket.  At this level of detail we don't
-- worry about certain forms being macros.
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Gambling.Racket where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal

type Var = Name Expr

-- term
data Expr =
  Var Var
  | StringLit String
  | QuoteSymbol String
  | Literal Literal
  | App [Expr]
  | Lam (Bind [Var] Body)
  | Let (Bind Bindings Body)
  | LetRec (Bind (Rec Bindings) Body)
  | Match Expr [Clause]
    deriving (Show, Generic, Typeable)
    

-- pattern
type Bindings = [Binding]

-- pattern
data Binding = Binding Var (Embed Expr)
             deriving (Show, Generic, Typeable)

-- term
newtype Clause =
  Clause (Bind Pattern Body)
  deriving (Show, Generic, Typeable)
  
-- pattern
data Pattern =
  VarP Var
  | WildP
  | ConsP Pattern Pattern
  | QuoteSymbolP (Embed String)
  deriving (Show, Generic, Typeable)

-- term
--
-- Racket calls these "internal definition contexts" and uses the
-- metavar /body/
newtype Body = Body (Bind (Rec [InternalDefn]) Expr)
             deriving (Show, Generic, Typeable)

-- pattern
data InternalDefn =
  DefnID Definition
  | ExprID (Embed Expr) -- no definition, just a bare expression
  deriving (Show, Generic, Typeable)
                           
-- pattern
data Definition = Define (Rebind Var (Embed Expr))
                deriving (Show, Generic, Typeable)

type ModuleIdentifier = Var
type ModuleLanguage = String

-- term
data Module = Module {
  _moduleId :: ModuleIdentifier
  , _moduleLanguage :: ModuleLanguage
  , _moduleBody :: ModuleDefnCtx
  }
            deriving (Show, Generic, Typeable)

-- term
newtype ModuleDefnCtx =
  ModuleDefnCtx (Bind (Rec [ModuleBinding]) Provides)
  deriving (Show, Generic, Typeable)
           
type ModulePath = String

-- pattern
data ModuleBinding =
  DefnMB Definition
  | ExprMB (Embed Expr)
  | RequireMB Requires
  deriving (Show, Generic, Typeable)

data RequirePath =
  RequireFilePath FilePath
  | RequireModulePath ModulePath
    deriving (Show, Generic, Typeable)

-- pattern
data Requires = Requires (Embed RequirePath) [Var]
              | RequiresAll (Embed RequirePath)
              deriving (Show, Generic, Typeable)

-- term
data Provides = Provides [Var]
              | ProvidesAll
              deriving (Show, Generic, Typeable)

instance Alpha Expr
instance Alpha Body
instance Alpha Binding
instance Alpha Clause
instance Alpha Pattern
instance Alpha InternalDefn
instance Alpha Definition
instance Alpha Provides
instance Alpha RequirePath
instance Alpha Requires
instance Alpha ModuleBinding
instance Alpha ModuleDefnCtx
instance Alpha Module
