{-# LANGUAGE
      MultiParamTypeClasses, 
      ViewPatterns,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.AST where

import Control.Applicative (Applicative(..), (<$>))
import Control.Lens.Traversal
import Control.Lens.Plated
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

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
          | Ann Expr Type
            deriving (Show, Typeable, Generic)

type AnnVar = (Var, Embed Annot)

mkAnnVar :: Var -> Annot -> AnnVar
mkAnnVar v a = (v, embed a)                

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

-- ========================================
-- Traversals

instance Plated Expr where
  plate _ (e@V {}) = pure e
  plate _ (e@C {}) = pure e
  plate _ (e@L {}) = pure e
  plate f (Lam bnd) =
    let (av, e) = UU.unsafeUnbind bnd
    in (Lam . bind av) <$> f e
  plate f (App e1 e2) =
    App <$> f e1 <*> f e2
  plate f (Case e clauses) =
    Case <$> f e <*> traverse (traverseExprs f) clauses
  plate f (Ann e t) =
    Ann <$> f e <*> pure t
  plate f (Let bnd) =
    let (bindings, e) = UU.unsafeUnbind bnd
    in Let <$> (bind <$> traverseExprs f bindings <*> f e)
       

class TraverseExprs s t where
  traverseExprs :: Traversal s t Expr Expr

instance TraverseExprs Clause Clause where
  traverseExprs f (Clause bnd) =
    let (pat, e) = UU.unsafeUnbind bnd
    in (Clause . bind pat) <$> f e

instance TraverseExprs Bindings Bindings where
  traverseExprs _ NilBs = pure NilBs
  traverseExprs f (ConsBs (unrebind -> (b1,bs))) =
    ConsBs <$> (rebind <$> traverseExprs f b1 <*> traverseExprs f bs)

instance TraverseExprs Binding Binding where
  traverseExprs f (LetB av (unembed -> e)) =
    (LetB av . embed) <$> f e
  traverseExprs f (SampleB av (unembed -> e)) =
    (SampleB av . embed) <$> f e

instance TraverseTypes Expr Expr where
  traverseTypes _ (e@V {}) = pure e
  traverseTypes _ (e@C {}) = pure e
  traverseTypes _ (e@L {}) = pure e
  traverseTypes f (Lam bnd) =
    let ((v,unembed -> ann), e) = UU.unsafeUnbind bnd
    in Lam <$> (bind <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e)
  traverseTypes _ (e@App {}) = pure e
  traverseTypes _ (e@Case {}) = pure e
  traverseTypes f (Let bnd) =
    let (bindings, e) = UU.unsafeUnbind bnd
    in Let <$> (bind <$> traverseTypes f bindings <*> pure e)
  traverseTypes f (Ann e t) =
    Ann e <$> f t

instance TraverseTypes Annot Annot where
  traverseTypes f (Annot Nothing) = pure (Annot Nothing)
  traverseTypes f (Annot (Just t)) = (Annot . Just) <$> f t

instance TraverseTypes Bindings Bindings where
  traverseTypes f NilBs = pure NilBs
  traverseTypes f (ConsBs (unrebind -> (b, bs))) =
    ConsBs <$> (rebind <$> traverseTypes f b <*> traverseTypes f bs)

instance TraverseTypes Binding Binding where
  traverseTypes f (LetB (v, unembed -> ann) e) =
    LetB <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e
  traverseTypes f (SampleB (v, unembed -> ann) e) =
    SampleB <$> (mkAnnVar v <$> traverseTypes f ann) <*> pure e
    
