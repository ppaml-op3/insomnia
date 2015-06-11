{-# LANGUAGE OverloadedStrings #-}
module Insomnia.Typecheck.Equiv.Types (equivTypes) where

import Data.Monoid ((<>))
import Control.Lens.Plated (plate)

import Insomnia.Types (Kind(..), Type(..))

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (expandAliasApplication)

import qualified Unbound.Generics.LocallyNameless as U

-- | Check that the two given types (of the specified kind) are
-- equivlant
equivTypes :: Type -> Type -> Kind -> TC Bool
equivTypes t1 t2 KType = checkEquivKType t1 t2
                         <??@ ("while checking " <> formatErr t1 <> " ≡ " <> formatErr t2)
equivTypes _t1 _t2 k = error ("finish implementing type equivalence at higher kind " ++ show k)

-- | Given two types of kind ⋆, check that they are equivalent by
-- expanding all type aliases visible in the current context and comparing
-- the results for alpha-equality.
checkEquivKType :: Type -> Type -> TC Bool
checkEquivKType t1_ t2_ = do
  t1 <- tcEverywhereInType expandIfPossibleAlias t1_
  t2 <- tcEverywhereInType expandIfPossibleAlias t2_
  return (t1 `U.aeq` t2)

tcEverywhereInType :: (Type -> TC Type) -> Type -> TC Type
tcEverywhereInType f t = do
  t' <- case t of
    TForall bnd -> do
      U.lunbind bnd $ \((tv, k), tbody) -> do
        tbody' <- extendTyVarCtx tv k $ tcEverywhereInType f tbody
        return $ TForall $ U.bind (tv, k) tbody'
    _ -> plate (tcEverywhereInType f) t
  f t'
  
-- | Try to expand the current head if it may be an alias.  Note that
-- the type may be under some number of applications.
expandIfPossibleAlias :: Type -> TC Type
expandIfPossibleAlias t =
  case t of
    TC {} -> do
      (t',_k) <- expandAliasApplication t []
      return t'
    TApp t1 t2 -> do
      (t',_k) <- expandAliasApplication t1 [t2]
      return t'
    _ -> return t
