{-# LANGUAGE
      MultiParamTypeClasses,
      FlexibleInstances, FlexibleContexts,
      DeriveDataTypeable, DeriveGeneric
  #-}
module TProb.Types where

import Control.Applicative
import Control.Lens.Prism
import Data.Typeable(Typeable)

import qualified Data.Text as T
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import TProb.Unify (UVar, Unifiable(..),
                    HasUVars(..),
                    Partial(..),
                    MonadUnify(..),
                    MonadUnificationExcept(..),
                    UnificationFailure(..))

-- At the term level, value constructor names.
-- At the type level, type constructor names.
newtype Con = Con { unCon :: String }
              deriving (Show, Eq, Ord, Typeable, Generic)
                       

type TyVar = Name Type
type KindedTVar = (TyVar, Kind)

data Kind = KType
          | KArr !Kind !Kind
            deriving (Show, Typeable, Generic)
infixr 6 `KArr`

data Type = TV TyVar
          | TUVar (UVar Type) -- invariant: unification variables should be fully applied
          | TC !Con
          | TAnn Type !Kind
          | TApp Type Type
          | TForall (Bind (TyVar, Kind) Type)
            deriving (Show, Typeable, Generic)

infixl 6 `TApp`

-- Alpha equivalence

instance Alpha Con
instance Alpha Type
instance Alpha Kind

-- Substitution

-- Capture avoiding substitution of type variables in types and terms.
instance Subst Type Type where
  isvar (TV v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Type Kind where
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

instance Partial Type where
  _UVar = let
    pick (TUVar u) = Just u
    pick _ = Nothing
    in prism' TUVar pick

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

-- | Construct a fresh unification var and apply it to fresh
-- unification vars for each of the arguments if it is of higher kind.
--   freshUnificationVar ⋆ = u
--   freshUnificationVar (k1 → ⋯ → kN → ⋆) = u·(map freshUnificationVar ks)
--
--  for example: ⌞a -> (b -> ⋆)⌟ = (u·⌞a⌟)·⌞b⌟
freshUnificationVar :: MonadUnify Type m => Kind -> m Type
freshUnificationVar = \ k -> do
  u <- unconstrained
  go k (TUVar u)
  where
    go KType thead = return thead
    go (KArr kdom kcod) thead = do
      targ <- freshUnificationVar kdom
      go kcod (thead `TApp` targ)

instance (MonadUnify Type m,
          MonadUnificationExcept Type m,
          LFresh m)
         => Unifiable Type m Type where
  t1 =?= t2 =
    case (t1, t2) of
      (TUVar u1, TUVar u2) | u1 == u2 -> return ()
      (TUVar u1, _)                   -> u1 -?= t2
      (_, TUVar u2)                   -> u2 -?= t1
      (TAnn t1' _, TAnn t2' _)        -> t1' =?= t2'
      (TAnn t1' _, _)                 -> t1' =?= t2
      (_, TAnn t2' _)                 -> t1 =?= t2'
      (TV v1, TV v2) | v1 == v2       -> return ()
      (TC c1, TC c2) | c1 == c2       -> return ()
      (TApp t11 t12, TApp t21 t22) -> do
        t11 =?= t21
        t12 =?= t22
      (TForall bnd1, TForall bnd2) ->
        lunbind2 bnd1 bnd2 $ \opn -> 
        case opn of
          Just ((_, _), t1', (_, _), t2') ->
            t1' =?= t2'
          Nothing -> throwUnificationFailure
                     $ Unsimplifiable (T.pack ("cannot unify"
                                               ++ show t1
                                               ++ " ≟ "
                                               ++ show t2))
      (TForall bnd1, _) ->
        lunbind bnd1 $ \ ((v1, k1), t1_) -> do
          tu1 <- freshUnificationVar k1
          let t1' = subst v1 tu1 t1_
          t1' =?= t2
      (ty1, TForall {}) -> t2 =?= t1
      _ -> throwUnificationFailure
           $ Unsimplifiable (T.pack ("cannot unify "
                                     ++ show t1 ++ " ≟ " ++ show t2))
