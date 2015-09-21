{-# LANGUAGE
      MultiParamTypeClasses,
      FlexibleInstances, FlexibleContexts,
      DeriveDataTypeable, DeriveGeneric
  #-}
module Insomnia.Types where

import Control.Applicative
import Control.Lens
import Control.Monad (liftM, zipWithM_)

import Data.Function (on)
import qualified Data.Map as M
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Typeable(Typeable)

import Data.Format (Format(..))
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier
import Insomnia.Common.Literal
import {-# SOURCE #-} Insomnia.ModuleType (ModuleType)

import Insomnia.Unify (UVar, Unifiable(..),
                    HasUVars(..),
                    Partial(..),
                    MonadUnify(..),
                    MonadUnificationExcept(..),
                    UnificationFailure(..))

type TyVar = Name Type
type KindedTVar = (TyVar, Kind)

type Nat = Integer

data Rows = Rows -- TODO


data Kind = KType -- ^ the kind of types
--          | KROW -- ^ the kind ROW of rows. users can't write it directly
          | KArr !Kind !Kind
            deriving (Show, Typeable, Generic)
infixr 6 `KArr`

-- | A local type constructor name.  These are similar to type variables, except they
-- are substituted by global type paths instead of by arbitrary types.
type TyConName = Name TypeConstructor

-- | A type path selects a type from a model named by field
data TypePath = TypePath Path Field
              deriving (Show, Eq, Ord, Typeable, Generic)

-- | A type constructor is either local to the current model, or it is
-- global.
data TypeConstructor =
  TCLocal TyConName
  | TCGlobal TypePath
  deriving (Show, Eq, Typeable, Generic)

instance Ord TypeConstructor where
  compare tc1 tc2 =
    case (tc1, tc2) of
     (TCLocal n1, TCLocal n2) -> compare n1 n2
     (TCLocal {}, TCGlobal {}) -> LT
     (TCGlobal {}, TCLocal {}) -> GT
     (TCGlobal p1, TCGlobal p2) -> compare p1 p2

-- | The types include type variables (which stand for types), unification
-- variables, type constructors, annotted kinds, type applications,
-- universally quantified types and record types.
data Type = TV TyVar
          | TUVar (UVar Kind Type) -- invariant: unification variables should be fully applied -- XXX what does this mean? ak-20150825
          | TC !TypeConstructor
          | TAnn Type !Kind
          | TApp Type Type
          | TForall (Bind (TyVar, Kind) Type)
          | TRecord Row
          | TPack !ModuleType -- first class modules of the given module type
          deriving (Show, Typeable, Generic)

infixl 6 `TApp`

-- | A label identifies a component of a row.
newtype Label = Label {labelName :: String}
              deriving (Show, Eq, Ord, Typeable, Generic)

-- | Rows associate a set of types with a set of labels.  For now this
-- is syntactically separate from other types and we don't have row
 -- variables, so this is really just plain old non-extensible records.
data Row = Row [(Label, Type)]
           deriving (Show, Typeable, Generic)

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

tForalls :: [(TyVar, Kind)] -> Type -> Type
tForalls [] = id
tForalls (tvk:tvks) = TForall . bind tvk . tForalls tvks

-- | Sort the labels of a row into a canonical order
canonicalOrderRowLabels :: [(Label, a)] -> [(Label, a)]
canonicalOrderRowLabels = sortBy (comparing fst)

-- Formatted output
instance Format Kind
instance Format Type

-- Alpha equivalence

instance Alpha Label
instance Alpha TypePath
instance Alpha TypeConstructor
instance Alpha Type
instance Alpha Kind
instance Alpha Row

instance Eq Type where
  (==) = aeq

-- Substitution

-- Capture avoiding substitution of type variables in types and terms.
instance Subst Type Type where
  isvar (TV v) = Just (SubstName v)
  isvar _ = Nothing
instance Subst Type Row

instance Subst Type Label where
  subst _ _ = id
  substs _ = id
instance Subst Type TypePath where
  subst _ _ = id
  substs _ = id
instance Subst Type Literal where
  subst _ _ = id
  substs _ = id
instance Subst Type Path where
  subst _ _ = id
  substs _ = id
instance Subst Type TypeConstructor where
  subst _ _ = id
  substs _ = id
instance Subst Type Kind where
  subst _ _ = id
  substs _ = id
-- unification variables are opaque boxes that can't be substituted into.
instance Subst Type (UVar w a) where
  subst _ _ = id
  substs _ = id
instance Subst Type SigPath where
  subst _ _ = id
  substs _ = id

instance Subst Path Kind where
  subst _ _ = id
  substs _ = id
instance Subst Path Label where
  subst _ _ = id
  substs _ = id


instance Subst Path TypePath
instance Subst Path TypeConstructor
instance Subst Path Type
instance Subst Path Row

instance Subst TypeConstructor TypeConstructor where
  isvar (TCLocal c) = Just (SubstName c)
  isvar _ = Nothing

instance Subst TypeConstructor TypePath where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor Path where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor SigPath where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor Literal where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor (UVar w a) where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor Label where
  subst _ _ = id
  substs _ = id
instance Subst TypeConstructor Kind where
  subst _ _ = id
  substs _ = id

instance Subst TypeConstructor Type
instance Subst TypeConstructor Row

-- Unification

instance Partial Kind Type where
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
      TPack {} -> pure t
      TForall bnd -> let
        (vk, t1) = UU.unsafeUnbind bnd
        in (TForall . bind vk) <$> allUVars f t1
      TRecord row -> TRecord <$> allUVars f row

instance HasUVars Type Row where
  allUVars f (Row ts) = Row <$> traverseOf (traverse . _2 . allUVars) f  ts
    

-- | Make a fresh unification variable
freshUVarT :: MonadUnify e Kind Type m => Kind -> m Type
freshUVarT k = liftM TUVar (unconstrained k)

-- | Construct a fresh type expression composed of a unification var
-- of the given kind applied to sufficiently many ground arguments
-- such that the whole type expression has of kind ⋆.
--
-- @      
--   ⌞⋆⌟ = u   - u fresh
--   ⌞k1 → ⋯ → kN → ⋆⌟ = apply u (map ⌞·⌟ ks)  - u fresh
-- @
--  for example: @⌞a -> (b -> ⋆)⌟ = (u·⌞a⌟)·⌞b⌟@
groundUnificationVar :: MonadUnify TypeUnificationError Kind Type m => Kind -> m Type
groundUnificationVar = \ k -> do
  tu <- freshUVarT k
  go k tu
  where
    go KType thead = return thead
    go (KArr kdom kcod) thead = do
      targ <- groundUnificationVar kdom
      go kcod (thead `TApp` targ)

data TypeUnificationError =
  SimplificationFail (M.Map (UVar Kind Type) Type) !Type !Type -- the two given types could not be simplified under the given constraints
  | RowLabelsDifferFail !Row !Row -- the two given rows could not be unifified because they have different labels
  | PackedModuleTypesDifferFail !ModuleType !ModuleType -- the two given module types are not equivalent

class MonadTypeAlias m where
  expandTypeAlias :: TypeConstructor -> m (Maybe Type)

instance (MonadUnify TypeUnificationError Kind Type m,
          MonadUnificationExcept TypeUnificationError Kind Type m,
          MonadTypeAlias m,
          LFresh m)
         => Unifiable Kind Type TypeUnificationError m Type where
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
      -- (TForall bnd1, _) ->
      --   lunbind bnd1 $ \ ((v1, _), t1_) -> do
      --     tu1 <- freshUVarT
      --     let t1' = subst v1 tu1 t1_
      --     t1' =?= t2
      -- (_, TForall {}) -> t2 =?= t1
      (TRecord row1, TRecord row2) -> row1 =?= row2
      (TPack modTy1, TPack modTy2) -> 
        if aeq modTy1 modTy2
        then return ()
        else throwUnificationFailure $ Unsimplifiable (PackedModuleTypesDifferFail modTy1 modTy2)

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


instance (MonadUnify TypeUnificationError Kind Type m,
          MonadUnificationExcept TypeUnificationError Kind Type m,
          MonadTypeAlias m,
          LFresh m)
         => Unifiable Kind Type TypeUnificationError m Row where
  r1@(Row ls1_) =?= r2@(Row ls2_) =
    let ls1 = canonicalOrderRowLabels ls1_
        ls2 = canonicalOrderRowLabels ls2_
    in if map fst ls1 == map fst ls2
       then zipWithM_ ((=?=) `on` snd) ls1 ls2
       else throwUnificationFailure $ Unsimplifiable (RowLabelsDifferFail r1 r2)

instance Plated Type where
  plate _ (t@TUVar {}) = pure t
  plate _ (t@TV {}) = pure t
  plate _ (t@TC {}) = pure t
  plate f (TPack modTy) = TPack <$> traverseTypes f modTy
  plate f (TForall bnd) =
    let (tvk,t) = UU.unsafeUnbind bnd
    in (TForall . bind tvk) <$> f t
  plate f (TAnn t k) = TAnn <$> f t <*> pure k
  plate f (TApp t1 t2) = TApp <$> f t1 <*> f t2
  plate f (TRecord ts) = TRecord <$> traverseTypes f ts

-- | Traverse the types in the given container
class TraverseTypes s t where
  traverseTypes :: Traversal s t Type Type

instance TraverseTypes Row Row where
  traverseTypes f (Row ts) = Row <$> traverseOf (traverse . _2) f ts

instance TraverseTypes a b => TraverseTypes (Maybe a) (Maybe b) where
  traverseTypes _ Nothing = pure Nothing
  traverseTypes f (Just a) = Just <$> traverseTypes f a

instance TraverseTypes a b => TraverseTypes [a] [b] where
  traverseTypes _ [] = pure []
  traverseTypes f (x:xs) = (:) <$> traverseTypes f x <*> traverseTypes f xs

transformEveryTypeM :: (TraverseTypes a a, Plated a, Monad m) => (Type -> m Type) -> a -> m a
transformEveryTypeM f = transformM (transformMOn traverseTypes f)
