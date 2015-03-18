{-# LANGUAGE
      MultiParamTypeClasses,
      FlexibleInstances,
      FlexibleContexts,
      UndecidableInstances,
      ScopedTypeVariables,
      DeriveDataTypeable,
      DeriveGeneric,
      FunctionalDependencies,
      OverloadedStrings,
      TemplateHaskell
  #-}
-- needs UndecidableInstances for the mtl classes.

-- | Somewhat generic implementation of first order unification.
-- The @'UnificationT' u@ monad transformer can add unification of
-- unification variables @'UVar' u@ that occur somewhere within a @u@.
-- In general the type @u@ (and perhaps others) will have to be instances
-- of @'Unifiable (UVar u) u@.
--
-- Note: We don't try to restrict the @UVar u@ values from escaping from the
-- unification monad via Haskell's typesystem, but you will get poor results
-- if they do so.  Caveat emptor!
module Insomnia.Unify
       (
         -- * Unification variables
         UVar
       , Partial(..)
       , HasUVars(..)
         -- * Terms subject to unification
       , Unifiable(..)
       , applyCurrentSubstitution
         -- * Unification monad class
       , MonadUnify(..)
       , MonadUnificationExcept(..)
         -- * The result of completely solving a unification subproblem.
       , UnificationResult(..)
       , UnificationFailure(..)
         -- * Unification monad transformer
       , UnificationT
       , evalUnificationT
       , runUnificationT
       ) where

import Control.Applicative (Applicative(..), (<$>))
import Control.Lens
import Control.Monad (when, liftM)
import Control.Monad.Trans.Class
import Control.Monad.State.Strict (StateT, MonadState(..))
import qualified Control.Monad.State.Strict as St
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Format (Format(..))
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(..), (<>), Endo(..))

import qualified Control.Monad.Reader.Class as Reader
import qualified Control.Monad.Error.Class as Error

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import qualified Unbound.Generics.LocallyNameless as U

-- | An unknown value of type @u@ to be discovered via unification.
newtype UVar u = UVar Int
             deriving (Eq, Ord, Typeable, Generic)

instance Format (UVar u) where
  format (UVar i) = "⁇" <> format i
instance Show (UVar u) where
  showsPrec _ (UVar i) = showString "⁇" . shows i
  
succUVar :: UVar u -> UVar u
succUVar (UVar i) = UVar $! i + 1

instance U.Alpha (UVar u)
  

newtype UnificationT u m b = UnificationT { ificationT :: StateT (S u) m b }

data UnificationResult e u b =
  UOkay b
  | UFail (UnificationFailure e u)

data UnificationFailure e u =
  CircularityOccurs !(UVar u) !u -- CircularityOccurs x e means x wants to unify with e which contains some subterm that is unified with x.
  | Unsimplifiable !e -- Simplification of a constraint x =?= y failed, for some x and y.

data EquivalenceClass a = EquivalenceClass {
  _equivReps :: M.Map a (Rep a)
  , _equivSiblings :: M.Map (Rep a) (S.Set a)
  }

newtype Rep a = Rep { canonicalRep :: a }
              deriving (Eq, Show, Ord)

data S u = S {
  _nextFreshId :: UVar u
  , _collectedConstraints :: M.Map (Rep (UVar u)) u --  invariant: no cycles
  , _equivalenceClasses :: EquivalenceClass (UVar u)
  }

$(makeLenses ''EquivalenceClass)
$(makeLenses ''S)

-- -------------------- Classes

-- | Types that are instances of partial may contain a unification
-- variable as one of their immediate constructors.
class Partial u where
  _UVar :: Prism' u (UVar u)
  
class HasUVars u b where
  allUVars :: Traversal' b u

class Monad m => MonadUnify e u m | m -> u e where
  unconstrained :: m (UVar u)
  solveUnification :: m b -> m (UnificationResult e u b)
  reflectCollectedConstraints :: m (M.Map (UVar u) u)

  (-?=) :: (Partial u, Unifiable u e m u) => (UVar u) -> u -> m ()

infix 4 =?=

class Monad m => MonadUnificationExcept e u m | m -> u e where
  throwUnificationFailure :: UnificationFailure e u -> m a

-- | Types @b@ that are unifiable with by solving for UVars that stand for
-- their @u@ subterms
class (MonadUnificationExcept e u m, HasUVars u b)
      => Unifiable u e m b | m -> u e where
  -- | traverse every unification variable in b.
  (=?=) :: b -> b -> m ()


-- ----------------------------------------

-- prism helper functions
  
isUVar :: Partial u => u -> Maybe (UVar u)
isUVar t = t ^? _UVar

injectUVar :: Partial u => UVar u -> u
injectUVar v = v^.re _UVar

-- -------------------- instances

instance HasUVars u b => HasUVars u [b] where
  allUVars _f [] = pure []
  allUVars f (b:bs) = (:) <$> allUVars f b <*> allUVars f bs

instance Functor m => Functor (UnificationT a m) where
  fmap f = UnificationT . fmap f . ificationT

instance (Functor m, Monad m) => Applicative (UnificationT a m) where
  pure = UnificationT . pure
  umf <*> umx = UnificationT (ificationT umf <*> ificationT umx)

instance Monad m => Monad (UnificationT a m) where
  return = UnificationT . return
  umx >>= umf = UnificationT $ 
    ificationT umx >>= \ x -> ificationT (umf x)

instance U.LFresh m => U.LFresh (UnificationT u m) where
  lfresh = UnificationT . U.lfresh
  avoid ns = UnificationT . U.avoid ns . ificationT
  getAvoids = UnificationT U.getAvoids

instance MonadTrans (UnificationT u) where
  lift = UnificationT . lift

instance Reader.MonadReader r m => Reader.MonadReader r (UnificationT u m) where
  ask = UnificationT Reader.ask
  local f = UnificationT . Reader.local f . ificationT
  reader = UnificationT . Reader.reader

instance Error.MonadError e m => Error.MonadError e (UnificationT u m) where
  throwError = UnificationT . Error.throwError
  catchError uma handler = UnificationT (ificationT uma
                                         `Error.catchError`
                                         (ificationT . handler))

instance (MonadUnificationExcept e u m)
         => MonadUnificationExcept e u (UnificationT u m) where
  throwUnificationFailure = UnificationT . lift . throwUnificationFailure

instance (Monad m, Partial u, MonadUnificationExcept e u (UnificationT u m))
         => MonadUnify e u (UnificationT u m) where
  unconstrained = instUnconstrained
  reflectCollectedConstraints = UnificationT $ summarizeConstraints
  solveUnification = instSolveUnification
  (-?=) = addConstraintUVar

-- if we ever need to delay solving some constraints, this would be
-- the place to force them.
instSolveUnification :: Monad m => UnificationT u m b -> UnificationT u m (UnificationResult e u b)
instSolveUnification comp = liftM UOkay comp

                            
instUnconstrained :: Monad m => UnificationT u m (UVar u)
instUnconstrained = do
  u <- UnificationT $ nextFreshId <<%= succUVar
  _ <- represent u
  return u

represent :: Monad m => UVar u -> UnificationT u m (Rep (UVar u))
represent u = UnificationT $ do
  eqc <- use equivalenceClasses
  let r = representative' u eqc
  case r of
   Just r -> return r
   Nothing -> do
     let r = Rep u
     (equivalenceClasses . equivReps) %= M.insert u r
     (equivalenceClasses . equivSiblings) %= M.insert r (S.singleton u)
     return r

addConstraintUVar :: (Partial u, Unifiable u e (UnificationT u m) u,
                      Monad m,
                      MonadUnificationExcept e u (UnificationT u m))
                     => UVar u -> u -> UnificationT u m ()
addConstraintUVar v t_ = do
  t <- applyCurrentSubstitution t_
  occursCheck v t
  t2 <- applyCurrentSubstitution (injectUVar v)
  case isUVar t2 of
    Just v' | v == v' -> return ()
            | otherwise -> UnificationT $ equivalenceClasses %= unite v v'
    _ -> t =?= t2
  case t^?_UVar of
   Nothing -> do
     r <- represent v
     UnificationT $ collectedConstraints . at r ?= t
   Just v'' -> UnificationT $ equivalenceClasses %= unite v v''

applyCurrentSubstitution :: (Partial u, Unifiable u e (UnificationT u m) u, Monad m)
                            => u -> UnificationT u m u
applyCurrentSubstitution = mapMOf allUVars replace
  where
    replace :: (Partial u, Unifiable u e (UnificationT u m) u, Monad m)
               => u -> UnificationT u m u
    replace t0 =
      case t0^?_UVar of
        Nothing -> return t0
        Just u -> do
          mt_ <- do 
            r <- represent u
            UnificationT $ use $ collectedConstraints . at r
          case mt_ of
            Nothing -> return t0
            Just t -> applyCurrentSubstitution t
      
occursCheck :: forall u e m .
               (Partial u, Monad m,
                Unifiable u e (UnificationT u m) u,
                MonadUnificationExcept e u (UnificationT u m))
               => UVar u -> u -> UnificationT u m ()
occursCheck v t = do
  r <- represent v
  let
    isV :: u -> UnificationT u m Bool
    isV t2 = do
        case (t2^?_UVar) of
         Just v' -> do
           r2 <- represent v'
           return $ r2 == r
         Nothing -> return False
  occs <- mapM isV (t^..allUVars)
  when (or occs) $ do
    throwUnificationFailure (CircularityOccurs v t)
  
-- | Run the unification monad transformer and return the computation
-- result, discarding the final unification state.
evalUnificationT :: Monad m => UnificationT u m a -> m a
evalUnificationT comp =
  St.evalStateT (ificationT comp) initialS

-- | Run the unification monad transformer and return the computation result
-- and the final map of constraints.
runUnificationT :: (Partial u, Monad m) => UnificationT u m a -> m (a, M.Map (UVar u) u)
runUnificationT comp =
  let stcomp = do
        a <- ificationT comp
        m <- summarizeConstraints
        return (a, m)
  in St.evalStateT stcomp initialS

summarizeConstraints :: (Partial u, MonadState (S u) m) => m (M.Map (UVar u) u)
summarizeConstraints = do
  mc_ <- use collectedConstraints
  mr_ <- use (equivalenceClasses . equivReps)
  let
    mc = M.mapKeysMonotonic canonicalRep mc_
    mr = fmap (injectUVar . canonicalRep) mr_
  return $ M.union mc mr -- prefer constraints to reps


initialS :: S u
initialS =
  S {
    _nextFreshId = UVar 0
    , _collectedConstraints = mempty
    , _equivalenceClasses =
      EquivalenceClass {
        _equivReps = mempty
        , _equivSiblings = mempty
        }
    }
           

-- equivalence classes
unite :: Ord a => a -> a -> EquivalenceClass a -> EquivalenceClass a
unite x y eqs = let
  (_, eqs') = unite' x y eqs
  in
   eqs'

unite' :: Ord a => a -> a -> EquivalenceClass a -> (Maybe (Rep a), EquivalenceClass a)
unite' x y eqs =
  let rx = representative x eqs
      ry = representative y eqs
  in case compare rx ry of
      LT -> (Just ry, go rx ry)
      EQ -> (Nothing, eqs)
      GT -> (Just rx, go ry rx)
  where
    -- go :: Ord b => b -> a -> b -> EquivalenceClass a
    go canonical other =
      let others = representedBy other eqs
      in eqs & equivReps %~ (appEndo $ mconcat $ map (\y -> Endo (M.insert y canonical)) $ S.toList others)
         & equivSiblings %~ (M.insert canonical (S.union (representedBy canonical eqs) others)
                             . M.delete other)

representedBy :: Ord a => (Rep a) -> EquivalenceClass a -> S.Set a
representedBy r eqs =
  fromMaybe S.empty $ M.lookup r (eqs^.equivSiblings)

representative :: Ord a => a -> EquivalenceClass a -> (Rep a)
representative x = fromMaybe (Rep x) . representative' x

representative' :: Ord a => a -> EquivalenceClass a -> Maybe (Rep a)
representative' x eqs = M.lookup x (eqs^.equivReps)
