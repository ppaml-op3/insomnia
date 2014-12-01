-- | Untyped lambda calculus for interpreter.
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}
module Insomnia.Interp.Lam where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Data.Function (on)
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal


type ConId = String

type Var = Name Value

data Expr =
  VarE !Var
  | ValE !Value
  | AppE !Expr !Expr
  | LamE !(Bind Var Expr)
  | CaseE !Expr ![Clause]
  | ConE !ConId ![Expr] -- saturated constructor application
  | ChooseE !Expr !Expr !Expr -- non-deterministic choice with given probability
  deriving (Show, Typeable, Generic)

data Program =
  EvalP !Expr
  | DefineP !(Bind Definition Program)
  deriving (Show, Typeable, Generic)

data Definition =
  VarDefn !Var !(Embed Expr)
  | FunDefn !Var !(Embed Expr) -- recursive defn, assuming expr is a lambda
  deriving (Show, Typeable, Generic)

data Value =
  CloV !(Bind (Env, Var) Expr)
  | LitV !Literal
  | ConV !ConId ![Value] -- saturated constructor application
  deriving (Show, Typeable, Generic)

newtype Clause =
  Clause (Bind Pattern Expr)
            deriving (Show, Typeable, Generic)
    
data Pattern =
  WildP
  | VarP !Var
  | ConP !(Embed ConId) ![Pattern]
  deriving (Show, Typeable, Generic)

newtype Env = Env { envMapping :: M.Map Var (Embed Value) }
            deriving (Show, Typeable)


instance Alpha Expr
instance Alpha Value
instance Alpha Clause
instance Alpha Pattern
instance Alpha Definition
instance Alpha Program

-- have to implement this one by hand.  Mostly via an isomorphism to a
-- sorted list of key-value pairs.  Except in a few places we take
-- advantage of the knowledge that the Env will only be used in
-- pattern position, never as a term.
instance Alpha Env where
  aeq' ctx = (aeq' ctx) `on` (M.toAscList . envMapping)
  fvAny' ctx nfn = fmap (Env . M.fromAscList) . fvAny' ctx nfn . (M.toAscList . envMapping)
  open ctx _b = if isTermCtx ctx
                then error "open of Env not in a pattern ctx"
                else id
  close ctx _b = if isTermCtx ctx
                 then error "close of Env not in a pattern ctx"
                 else id
  isPat = isPat . (M.toAscList . envMapping)
  isTerm = const False
  nthPatFind = nthPatFind . (M.toAscList . envMapping)
  namePatFind = namePatFind . (M.toAscList . envMapping)
  swaps' ctx _p =
    if isTermCtx ctx
    then error "swaps' of Env not in a pattern ctx"
    else id
  freshen' ctx e = do
    let l = M.toAscList $ envMapping e
    (l', perm) <- freshen' ctx l
    -- Would like to use fromAscList here, but I'm not sure that
    -- the calls to freshen' will always return the keys in a monotonic order.
    return (Env $ M.fromList l', perm)
  lfreshen' ctx e cont = do
    let l = M.toAscList $ envMapping e
    lfreshen' ctx l $ \l' perm -> cont (Env $ M.fromList l') perm

{- 
instance Subst Value Value
instance Subst Value Literal where
  subst _ _ = id
  substs _ = id
instance Subst Value Expr where
  isCoerceVar (VarE v) = Just (SubstCoerce v (Just . ValE))
  isCoerceVar _ = Nothing
instance Subst Value Clause

-- We may be asked to substitute into an Env if we have to substitute
-- into a ValE which is a CloV (which itself ought to short circuit
-- and bail out.) So we could, in theory, be asked to substitute into
-- the values in the domain of the environment.  But literals are
-- trivially closed and closures are closed by definition.  Therefore
-- there can be no free variables in the domain of the environment.
-- Therefore this substitution operation is the identity.
instance Subst Value Env where
  subst _ _ = id
  substs _ = id
--  subst nm val = Env . M.map (subst nm val) . envMapping
--  substs s = Env . M.map (substs s) . envMapping

-}
