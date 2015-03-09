-- | Core Insomnia expression language.
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses, ViewPatterns
  #-}
module Insomnia.Expr where

import Control.Applicative (Applicative(..), (<$>))
import Control.Lens.Traversal
import Control.Lens.Fold (anyOf)
import Control.Lens.Plated
import Control.Lens.Tuple (_2)
import Control.Lens.Iso (iso)

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Common.Literal
import Insomnia.Common.Telescope
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn (TypeDefn, TypeAlias, ValueConstructor)

type Var = Name Expr

-- | Qualified variables - references to other modules.
data QVar = QVar !Path !Field
             deriving (Show, Eq, Ord, Typeable, Generic)

data Expr = V !Var
          | Q !QVar -- qualified variable: Foo.Bar.t
          | C !ValueConstructor
          | L !Literal
          | Lam !(Bind AnnVar Expr)
          | Record ![(Label, Expr)]
          | App !Expr !Expr
          | Case !Expr ![Clause] !Annot -- result type
          | Let !(Bind Bindings Expr)
          | Ann !Expr !Type
          | Return !Expr
            -- | internal node for explicit instantiation.  The type
            -- unification algorithm inserts these.
          | Instantiate !Expr !InstantiationCoercion
            deriving (Show, Typeable, Generic)

type TypeScheme = Type

-- | Instantiation coercions record evidence for the instantiation of
-- a polymorphic function with some (perhaps zero) arguments.
data InstantiationCoercion =
  InstantiationSynthesisCoercion !TypeScheme ![Type] !Type -- ∀αs.ρ ≤ [αs↦τs]ρ
  deriving (Show, Typeable, Generic)

type AnnVar = (Var, Embed Annot)

mkAnnVar :: Var -> Annot -> AnnVar
mkAnnVar v a = (v, embed a)                

newtype Annot = Annot (Maybe Type)
              deriving (Show, Typeable, Generic)

-- | A sequence of bindings, each of which brings variables into scope in the
-- RHSs of the rest.  (ie, let* from Scheme)
newtype Bindings = Bindings { bindingsTele :: Telescope Binding }
                 deriving (Show, Typeable, Generic)

-- | A single binding that binds the result of some kind of RHS to a variable.
data Binding = ValB AnnVar (Embed Expr)
             | SampleB AnnVar (Embed Expr)
             | TabB Var (Embed TabulatedFun)
             deriving (Show, Typeable, Generic)

-- | A clause in a case expression
newtype Clause = Clause (Bind Pattern Expr)
                 deriving (Show, Typeable, Generic)

-- | A "forall (x :: T1) (x2 :: T2) in y <selectors> ~ <expr>" style binder
-- that defines a function by tabulation.
--
-- The scoping here is:
--   1. y is in scope for the remainder of the enclosing let expression.
--   2. the xs are in scope in <selectors> and <expr>.
data TabulatedFun = TabulatedFun (Bind [AnnVar] TabSample)
               deriving (Show, Typeable, Generic)

-- | the "... x1 x2 ~ e" part of a TabulatedFun
data TabSample = TabSample ![TabSelector] !Expr
                 deriving (Show, Typeable, Generic)

-- | The selectors that may appear in the "argument position" of
-- the ForBind form.  Right now, just variables.
data TabSelector =
  TabIndex Var -- select table entry by a variable
  deriving (Show, Typeable, Generic)

-- | A pattern in a case expression
data Pattern = WildcardP
             | VarP Var
             | ConP !(Embed ValueConstructor) [Pattern]
             | RecordP ![(Embed Label, Pattern)]
               deriving (Show, Typeable, Generic)

-- | @anyBindings predicate bs@ returns 'True' iff @predicate@ returns
-- @True@ for any of the given @bs@
anyBindings :: (Binding -> Bool) -> Bindings -> Bool
anyBindings p = anyOf traverseTelescope p . bindingsTele

-- | Return 'True' if the given binding is a SampleB or a TabB
isStochasticBinding :: Binding -> Bool
isStochasticBinding (SampleB {}) = True
isStochasticBinding (TabB {}) = True
isStochasticBinding (ValB {}) = False

-- All these types have notions of alpha equivalence upto bound
-- term and type variables.
instance Alpha Expr
instance Alpha InstantiationCoercion
instance Alpha QVar
instance Alpha Pattern
instance Alpha Clause
instance Alpha Bindings
instance Alpha Binding
instance Alpha Annot
instance Alpha TabulatedFun
instance Alpha TabSample
instance Alpha TabSelector

instance Eq Expr where (==) = aeq
instance Eq Clause where (==) = aeq

-- Capture-avoiding substitution of term variables in terms
instance Subst Expr Expr where
  isvar (V v) = Just (SubstName v)
  isvar _ = Nothing
instance Subst Expr Clause
instance Subst Expr Pattern

instance Subst Expr Bindings
instance Subst Expr Binding

instance Subst Expr TabulatedFun
instance Subst Expr TabSample

-- Capture avoid substitution of types for type variables in the following.
instance Subst Type InstantiationCoercion
instance Subst Type Clause
instance Subst Type Pattern
instance Subst Type Expr
instance Subst Type Annot
instance Subst Type Bindings
instance Subst Type Binding
instance Subst Type TabulatedFun
instance Subst Type TabSample

instance Subst Path Expr
instance Subst Path InstantiationCoercion
instance Subst Path QVar
instance Subst Path Annot
instance Subst Path Bindings
instance Subst Path Binding
instance Subst Path Clause
instance Subst Path Pattern
instance Subst Path TabulatedFun
instance Subst Path TabSample

instance Subst ValueConstructor Expr
instance Subst ValueConstructor Pattern
instance Subst ValueConstructor Bindings
instance Subst ValueConstructor Binding
instance Subst ValueConstructor TabulatedFun
instance Subst ValueConstructor TabSample
instance Subst ValueConstructor Clause
instance Subst ValueConstructor TabSelector

instance Subst TypeConstructor Expr
instance Subst TypeConstructor InstantiationCoercion
instance Subst TypeConstructor Pattern
instance Subst TypeConstructor Annot
instance Subst TypeConstructor Bindings
instance Subst TypeConstructor Binding
instance Subst TypeConstructor TabulatedFun
instance Subst TypeConstructor TabSample
instance Subst TypeConstructor Clause


-- leaf instances
instance Subst Expr Path where
  subst _ _ = id
  substs _ = id
instance Subst Expr QVar where
  subst _ _ = id
  substs _ = id
instance Subst Expr Literal where
  subst _ _ = id
  substs _ = id
instance Subst Expr Annot where
  subst _ _ = id
  substs _ = id
instance Subst Expr TabSelector where
  subst _ _ = id
  substs _ = id
instance Subst Expr Label where
  subst _ _ = id
  substs _ = id
instance Subst Expr Type where
  subst _ _ = id
  substs _ = id
instance Subst Expr TypeDefn where
  subst _ _ = id
  substs _ = id
instance Subst Expr TypeAlias where
  subst _ _ = id
  substs _ = id
instance Subst Expr ValueConstructor where
  subst _ _ = id
  substs _ = id

instance Subst Type TabSelector where
  subst _ _ = id
  substs _ = id
instance Subst Type QVar where
  subst _ _ = id
  substs _ = id

instance Subst Path TabSelector where
  subst _ _ = id
  substs _ = id

instance Subst ValueConstructor InstantiationCoercion where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor QVar where
  subst _ _ = id
  substs _ = id
instance Subst ValueConstructor Annot where
  subst _ _ = id
  substs _ = id

instance Subst TypeConstructor QVar where
  subst _ _ = id
  substs _ = id

instance Subst TypeConstructor TabSelector where
  subst _ _ = id
  substs _ = id

instance Subst Expr InstantiationCoercion where
  subst _ _ = id
  substs _ = id

-- ========================================
-- Traversals

instance Plated Expr where
  plate _ (e@V {}) = pure e
  plate _ (e@Q {}) = pure e
  plate _ (e@C {}) = pure e
  plate _ (e@L {}) = pure e
  plate f (Lam bnd) =
    let (av, e) = UU.unsafeUnbind bnd
    in (Lam . bind av) <$> f e
  plate f (App e1 e2) =
    App <$> f e1 <*> f e2
  plate f (Case e clauses ann) =
    Case <$> f e <*> traverse (traverseExprs f) clauses <*> pure ann
  plate f (Ann e t) =
    Ann <$> f e <*> pure t
  plate f (Record les) =
    Record <$> traverseOf (traverse . _2) f les
  plate f (Let bnd) =
    let (bindings, e) = UU.unsafeUnbind bnd
    in Let <$> (bind <$> traverseExprs f bindings <*> f e)
  plate f (Return e) = Return <$> f e
  plate f (Instantiate e co) = Instantiate <$> f e <*> pure co

class TraverseExprs s t where
  traverseExprs :: Traversal s t Expr Expr

instance TraverseExprs Clause Clause where
  traverseExprs f (Clause bnd) =
    let (pat, e) = UU.unsafeUnbind bnd
    in (Clause . bind pat) <$> f e

instance TraverseExprs Bindings Bindings where
  traverseExprs = iso bindingsTele Bindings . traverseTelescope . traverseExprs

instance TraverseExprs Binding Binding where
  traverseExprs f (ValB av (unembed -> e)) =
    (ValB av . embed) <$> f e
  traverseExprs f (SampleB av (unembed -> e)) =
    (SampleB av . embed) <$> f e
  traverseExprs f (TabB v (unembed -> tf)) =
    (TabB v . embed) <$> traverseExprs f tf

instance TraverseExprs TabulatedFun TabulatedFun where
  traverseExprs f (TabulatedFun bnd) =
    let (avs, ts) = UU.unsafeUnbind bnd
    in (TabulatedFun . bind avs) <$> traverseExprs f ts

instance TraverseExprs TabSample TabSample where
  traverseExprs f (TabSample sels e) =
    TabSample sels <$> f e

instance TraverseTypes Expr Expr where
  traverseTypes _ (e@V {}) = pure e
  traverseTypes _ (e@Q {}) = pure e
  traverseTypes _ (e@C {}) = pure e
  traverseTypes _ (e@L {}) = pure e
  traverseTypes _ e@(Return {}) = pure e
  traverseTypes f (Lam bnd) =
    let ((v,unembed -> ann), e) = UU.unsafeUnbind bnd
    in Lam <$> (bind <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e)
  traverseTypes _ (e@App {}) = pure e
  traverseTypes f (Case subj clauses ann) =
    Case <$> pure subj <*> pure clauses <*> traverseTypes f ann
  traverseTypes _ (e@Record {}) = pure e
  traverseTypes f (Let bnd) =
    let (bindings, e) = UU.unsafeUnbind bnd
    in Let <$> (bind <$> traverseTypes f bindings <*> pure e)
  traverseTypes f (Ann e t) =
    Ann e <$> f t
  traverseTypes f (Instantiate e co) =
    Instantiate <$> pure e <*> traverseTypes f co

instance TraverseTypes InstantiationCoercion InstantiationCoercion where
  traverseTypes f (InstantiationSynthesisCoercion sigma ts rho) =
    InstantiationSynthesisCoercion <$> f sigma <*> traverse f ts <*> f rho

instance TraverseTypes Annot Annot where
  traverseTypes _ (Annot Nothing) = pure (Annot Nothing)
  traverseTypes f (Annot (Just t)) = (Annot . Just) <$> f t

instance TraverseTypes Bindings Bindings where
  traverseTypes = iso bindingsTele Bindings . traverseTelescope . traverseTypes

instance TraverseTypes Binding Binding where
  traverseTypes f (ValB (v, unembed -> ann) e) =
    ValB <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e
  traverseTypes f (SampleB (v, unembed -> ann) e) =
    SampleB <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e
  traverseTypes f (TabB v (unembed -> tf)) =
    (TabB v . embed) <$> traverseTypes f tf

instance TraverseTypes TabulatedFun TabulatedFun where
  traverseTypes f (TabulatedFun bnd) =
    let (avs, ts) = UU.unsafeUnbind bnd
    in TabulatedFun <$> (bind <$> traverseOf (traverse
                                              ._2
                                              .iso unembed Embed
                                              . traverseTypes) f avs
                         <*> pure ts)
