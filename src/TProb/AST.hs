{-# LANGUAGE
      MultiParamTypeClasses, 
      DeriveDataTypeable, DeriveGeneric
  #-}
module TProb.AST where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

import TProb.Types

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
  deriving (Show)

-- a DataDecl of kind k1 -> ... -> kN -> * with the given construtors.
type DataDecl = Bind [KindedTVar] [ConstructorDef]

data ConstructorDef = ConstructorDef !Con [Type]
                    deriving (Show, Typeable, Generic)

data Literal = IntL Integer
             | DoubleL Double
             deriving (Show, Typeable, Generic)
                      
data Expr = V Var
          | C !Con
          | L !Literal
          | Lam (Bind AnnVar Expr)
          | App Expr Expr
          | Let (Bind [Binding] Expr)
          | Sample (Bind (Var, Embed Expr) Expr)
          | Ann Expr Type
            deriving (Show, Typeable, Generic)

type AnnVar = (Var, Embed Annot)

newtype Annot = Annot (Maybe Type)
              deriving (Show, Typeable, Generic)

data Binding = LetB AnnVar (Embed Expr)
             | SampleB AnnVar (Embed Expr)
             deriving (Show, Typeable, Generic)


-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha Expr
instance Alpha Literal
instance Alpha Binding
instance Alpha Annot
instance Alpha ConstructorDef

-- Capture-avoiding substitution of term variables in terms
instance Subst Expr Expr where
  isvar (V v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Expr Binding

instance Subst Type Expr
instance Subst Type Annot
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

