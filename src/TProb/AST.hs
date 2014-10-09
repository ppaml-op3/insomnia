{-# LANGUAGE
      MultiParamTypeClasses,
      FlexibleInstances, FlexibleContexts,
      DeriveDataTypeable, DeriveGeneric
  #-}
module TProb.AST where

import Control.Applicative
import Data.Typeable(Typeable)
import qualified Data.Text as T
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import TProb.Unify (UVar, Unifiable(..),
                    HasUVars(..),
                    MonadUnify(..),
                    MonadUnificationExcept(..),
                    UnificationFailure(..))

type Var = Name Expr

-- At the term level, value constructor names.
-- At the type level, type constructor names.
newtype Con = Con { unCon :: String }
              deriving (Show, Eq, Ord, Typeable, Generic)
                       
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

type KindedTVar = (TyVar, Kind)

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

data Kind = KType
          | KArr !Kind !Kind
            deriving (Show, Typeable, Generic)
infixr 6 `KArr`

type TyVar = Name Type

data Type = TV TyVar
          | TUVar (UVar Type) -- invariant: unification variables should be fully applied
          | TC !Con
          | TAnn Type !Kind
          | TApp Type Type
          | TForall (Bind (TyVar, Kind) Type)
            deriving (Show, Typeable, Generic)

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha Expr
instance Alpha Literal
instance Alpha Binding
instance Alpha Annot
instance Alpha Con
instance Alpha Type
instance Alpha Kind
instance Alpha ConstructorDef

-- Capture-avoiding substitution of term variables in terms
instance Subst Expr Expr where
  isvar (V v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Expr Binding

-- Capture avoiding substitution of type variables in types and terms.
instance Subst Type Type where
  isvar (TV v) = Just (SubstName v)
  isvar _ = Nothing

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

instance Subst Type Kind where
  subst _ _ = id
  substs _ = id
instance Subst Type Literal where
  subst _ _ = id
  substs _ = id
instance Subst Type Con where
  subst _ _ = id
  substs _ = id
-- unification variables are opaque boxes that can't be substituted into.
instance Subst Type (UVar a) where
  subst _ _ = id
  substs _ = id

-- Unification

instance HasUVars Type Type where
  allUVars f t =
    case t of
      TV {} -> pure t
      TUVar uvar -> f t
      TC {} -> pure t
      TAnn t k -> TAnn <$> allUVars f t <*> pure k
      TApp t1 t2 -> TApp <$> allUVars f t1 <*> allUVars f t2
      TForall bnd -> let
        (vk, t) = UU.unsafeUnbind bnd
        in (TForall . bind vk) <$> allUVars f t

instance (MonadUnify Type m,
          MonadUnificationExcept Type m)
         => Unifiable Type m Type where
  t1 =?= t2 =
    case (t1, t2) of
      _ -> throwUnificationFailure
           $ Unsimplifiable (T.pack ("unimplemented simplification for "
                                     ++ show t1 ++ " ≟ " ++ show t2))
