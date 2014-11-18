{-# LANGUAGE
      MultiParamTypeClasses,
      FlexibleInstances, FlexibleContexts,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.Types where

import Control.Applicative
import Control.Lens
import Control.Monad (liftM)

import qualified Data.Map as M
import Data.Typeable(Typeable)

import Data.Format (Format(..))
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier

import Insomnia.Unify (UVar, Unifiable(..),
                    HasUVars(..),
                    Partial(..),
                    MonadUnify(..),
                    MonadUnificationExcept(..),
                    UnificationFailure(..))

-- | A qualified name.
-- At the term level, value constructor names.
-- At the type level, type constructor names.
newtype Con = Con { unCon :: Path }
              deriving (Show, Eq, Ord, Typeable, Generic)
                       
-- | A short type constructor name.  The parser makes these when it
-- sees unqualified Uppercase identifiers in positions where it
-- expects a type.
type ShortCon = Con

type TyVar = Name Type
type KindedTVar = (TyVar, Kind)

type Nat = Integer

data Rows = Rows -- TODO


data Kind = KType -- ^ the kind of types
--          | KROW -- ^ the kind ROW of rows. users can't write it directly
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

-- | iterate kind arrow construction
-- @kArrs [k1, ... kN] kcod = k1 `KArr` k2 `KArr` ... `KArr` kN `kArr` kcod@
kArrs :: [Kind] -> Kind -> Kind
kArrs [] kcod = kcod
kArrs (kdom:ks) kcod = kdom `KArr` kArrs ks kcod

-- | iterate type application
-- @tApps t0 [t1, ..., tN] = t0 `TApp` t1 `TApp` ... `TApp` tN
tApps :: Type -> [Type] -> Type
tApps t0 [] = t0
tApps t0 (t1:ts) = tApps (TApp t0 t1) ts

-- Formatted output
instance Format Con
instance Format Kind
instance Format Type

-- Alpha equivalence

instance Alpha Con
instance Alpha Type
instance Alpha Kind

-- Substitution

-- Capture avoiding substitution of type variables in types and terms.
instance Subst Type Type where
  isvar (TV v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst Type Path where
  subst _ _ = id
  substs _ = id
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
instance Subst Path Kind where
  subst _ _ = id
  substs _ = id

instance Subst Path Con
instance Subst Path Type

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
      TUVar {} -> f t
      TC {} -> pure t
      TAnn t1 k -> TAnn <$> allUVars f t1 <*> pure k
      TApp t1 t2 -> TApp <$> allUVars f t1 <*> allUVars f t2
      TForall bnd -> let
        (vk, t1) = UU.unsafeUnbind bnd
        in (TForall . bind vk) <$> allUVars f t1

-- | Make a fresh unification variable
freshUVarT :: MonadUnify e Type m => m Type
freshUVarT = liftM TUVar unconstrained

-- | Construct a fresh type expression composed of a unification var
-- of the given kind applied to sufficiently many ground arguments
-- such that the whole type expression has of kind ⋆.
--
-- @      
--   ⌞⋆⌟ = u   - u fresh
--   ⌞k1 → ⋯ → kN → ⋆⌟ = apply u (map ⌞·⌟ ks)  - u fresh
-- @
--  for example: @⌞a -> (b -> ⋆)⌟ = (u·⌞a⌟)·⌞b⌟@
groundUnificationVar :: MonadUnify TypeUnificationError Type m => Kind -> m Type
groundUnificationVar = \ k -> do
  tu <- freshUVarT
  go k tu
  where
    go KType thead = return thead
    go (KArr kdom kcod) thead = do
      targ <- groundUnificationVar kdom
      go kcod (thead `TApp` targ)

data TypeUnificationError =
  SimplificationFail (M.Map (UVar Type) Type) !Type !Type -- the two given types could not be simplified under the given constraints

class MonadTypeAlias m where
  expandTypeAlias :: Con -> m (Maybe Type)

instance (MonadUnify TypeUnificationError Type m,
          MonadUnificationExcept TypeUnificationError Type m,
          MonadTypeAlias m,
          LFresh m)
         => Unifiable Type TypeUnificationError m Type where
  t1 =?= t2 =
    case (t1, t2) of
      (TForall bnd1, TForall bnd2) ->
        lunbind2 bnd1 bnd2 $ \opn -> 
        case opn of
          Just ((_, _), t1', (_, _), t2') ->
            t1' =?= t2'
          Nothing -> do
            constraintMap <- reflectCollectedConstraints
            throwUnificationFailure
              $ Unsimplifiable (SimplificationFail constraintMap t1 t2)
      (TForall bnd1, _) ->
        lunbind bnd1 $ \ ((v1, _), t1_) -> do
          tu1 <- freshUVarT
          let t1' = subst v1 tu1 t1_
          t1' =?= t2
      (_, TForall {}) -> t2 =?= t1
      (TUVar u1, TUVar u2) | u1 == u2 -> return ()
      (TUVar u1, _)                   -> u1 -?= t2
      (_, TUVar u2)                   -> u2 -?= t1
      (TAnn t1' _, TAnn t2' _)        -> t1' =?= t2'
      (TAnn t1' _, _)                 -> t1' =?= t2
      (_, TAnn t2' _)                 -> t1 =?= t2'
      (TV v1, TV v2) | v1 == v2       -> return ()
      (TC c1, TC c2)                  ->
        if c1 == c2
        then return ()
        else do
          mexp1 <- expandTypeAlias c1
          mexp2 <- expandTypeAlias c2
          case (mexp1, mexp2) of
           (Just t1', Just t2') -> t1' =?= t2'
           (Just t1', Nothing) -> t1' =?= t2
           (Nothing, Just t2') -> t1 =?= t2'
           (Nothing, Nothing) -> failedToUnify
      (TC c1, _) -> do
        mexp <- expandTypeAlias c1
        case mexp of
         Nothing -> failedToUnify
         Just t1' -> t1' =?= t2
      (_, TC _c2) -> t2 =?= t1
      (TApp t11 t12, TApp t21 t22) -> do
        t11 =?= t21
        t12 =?= t22
      _ -> failedToUnify
    where
      failedToUnify = do
        constraintMap <- reflectCollectedConstraints
        throwUnificationFailure
          $ Unsimplifiable (SimplificationFail constraintMap t1 t2)

-- | note that this 'Traversal'' does not descend under binders.  The passed
-- function should explore TForall on its own.
instance Plated Type where
  plate _ (t@TUVar {}) = pure t
  plate _ (t@TV {}) = pure t
  plate _ (t@TC {}) = pure t
  plate _ (t@TForall {}) = pure t
  plate f (TAnn t k) = TAnn <$> f t <*> pure k
  plate f (TApp t1 t2) = TApp <$> f t1 <*> f t2

-- | Traverse the types in the given container
class TraverseTypes s t where
  traverseTypes :: Traversal s t Type Type

instance TraverseTypes Type Type where
  traverseTypes = plate

transformEveryTypeM :: (TraverseTypes a a, Plated a, Monad m) => (Type -> m Type) -> a -> m a
transformEveryTypeM f = transformM (transformMOn traverseTypes f)
