{-# LANGUAGE
      MultiParamTypeClasses, 
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.AST where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import Insomnia.Types

type Var = Name Expr

-- A single module.
data Module = Module { moduleDecls :: [Decl] }
              deriving (Show)

-- | A declaration
data Decl =
  FunDecl !Var !Expr     -- ^ function definition "fun f x = ..."
  | SigDecl !Var !Type   -- ^ a function signature "sig f :: A -> B"
    -- | "data T (a::K)... = C1 T11 ... T1m | C2 | C3 T31 ... T3n"
  | DataDecl !Con !DataDecl
  | EnumDecl !Con !Nat
  deriving (Show)

-- a DataDecl of kind k1 -> ... -> kN -> * with the given construtors.
type DataDecl = Bind [KindedTVar] [ConstructorDef]

data ConstructorDef = ConstructorDef !Con [Type]
                    deriving (Show, Typeable, Generic)

data Literal = IntL Integer
             | RealL Double
             deriving (Show, Typeable, Generic)
                      
data Expr = V Var
          | C !Con
          | L !Literal
          | Lam (Bind AnnVar Expr)
          | App Expr Expr
          | Case Expr [Clause]
          | Let (Bind Bindings Expr)
          | Sample (Bind (Var, Embed Expr) Expr)
          | Ann Expr Type
            deriving (Show, Typeable, Generic)

type AnnVar = (Var, Embed Annot)

newtype Annot = Annot (Maybe Type)
              deriving (Show, Typeable, Generic)

-- | A sequence of bindings, each of which brings variables into scope in the
-- RHSs of the rest.  (ie, let* from Scheme)
data Bindings = NilBs
              | ConsBs (Rebind Binding Bindings)
                deriving (Show, Typeable, Generic)

-- | A single binding that binds the result of some kind of RHS to a variable.
data Binding = LetB AnnVar (Embed Expr)
             | SampleB AnnVar (Embed Expr)
             deriving (Show, Typeable, Generic)

-- | A clause in a case expression
newtype Clause = Clause (Bind Pattern Expr)
                 deriving (Show, Typeable, Generic)

-- | A pattern in a case expression
data Pattern = WildcardP
             | VarP Var
             | ConP !Con [Pattern]
               deriving (Show, Typeable, Generic)

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha Expr
instance Alpha Pattern
instance Alpha Clause
instance Alpha Literal
instance Alpha Bindings
instance Alpha Binding
instance Alpha Annot
instance Alpha ConstructorDef

-- Capture-avoiding substitution of term variables in terms
instance Subst Expr Expr where
  isvar (V v) = Just (SubstName v)
  isvar _ = Nothing
instance Subst Expr Clause
instance Subst Expr Pattern

instance Subst Expr Bindings
instance Subst Expr Binding

instance Subst Type Clause
instance Subst Type Pattern
instance Subst Type Expr
instance Subst Type Annot
instance Subst Type Bindings
instance Subst Type Binding
instance Subst Type ConstructorDef

-- leaf instances
instance Subst Expr Con where
  subst _ _ = id
  substs _ = id
instance Subst Expr Literal where
  subst _ _ = id
  substs _ = id
instance Subst Expr Annot where
  subst _ _ = id
  substs _ = id
instance Subst Expr Type where
  subst _ _ = id
  substs _ = id

instance Subst Type Literal where
  subst _ _ = id
  substs _ = id

