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
       , uvarClassifier
       , Partial(..)
       , HasUVars(..)
         -- * Terms subject to unification
       , Unifiable(..)
       , applyCurrentSubstitution
         -- * Unification monad class
       , MonadUnify(..)
       , MonadUnificationExcept(..)
       , MonadCheckpointUnification(..)
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

-- | An unknown value of type @u@ (with aux info @w@) to be discovered via unification.
data UVar w u = UVar !Int w
             deriving (Typeable, Generic)

-- | a Lens that targets the carried classifier of a @UVar u@.
--
-- @@@
--    uvarClassifier :: Lens (UVar w u) (UVar w' u) w w'
-- @@@
uvarClassifier :: Functor f => (w -> f w') -> UVar w u -> f (UVar w' u)
uvarClassifier f (UVar i w) = fmap (UVar i) (f w)



instance Eq (UVar w u) where
  UVar i _ == UVar j _ = i == j

instance Ord (UVar w u) where
  compare (UVar i _) (UVar j _) = compare i j

instance Format (UVar w u) where
  format (UVar i _) = "⁇" <> format i
instance Show (UVar w u) where
  showsPrec _ (UVar i _) = showString "⁇" . shows i
  
instance U.Alpha w => U.Alpha (UVar w u)
  

newtype UnificationT w u m b = UnificationT { ificationT :: StateT (S w u) m b }

data UnificationResult e w u b =
  UOkay b
  | UFail (UnificationFailure e w u)

data UnificationFailure e w u =
  CircularityOccurs !(UVar w u) !u -- CircularityOccurs x e means x wants to unify with e which contains some subterm that is unified with x.
  | Unsimplifiable !e -- Simplification of a constraint x =?= y failed, for some x and y.

data EquivalenceClass a = EquivalenceClass {
  _equivReps :: M.Map a (Rep a)
  , _equivSiblings :: M.Map (Rep a) (S.Set a)
  }
                        deriving (Show)

newtype Rep a = Rep { canonicalRep :: a }
              deriving (Eq, Show, Ord)

data S w u = S {
  _nextFreshId :: Int
  , _collectedConstraints :: M.Map (Rep (UVar w u)) u --  invariant: no cycles
  , _equivalenceClasses :: EquivalenceClass (UVar w u)
  }

$(makeLenses ''EquivalenceClass)
$(makeLenses ''S)

-- -------------------- Classes

-- | Types that are instances of partial may contain a unification
-- variable as one of their immediate constructors.
class Partial w u | u -> w where
  _UVar :: Prism' u (UVar w u)
  
class HasUVars u b where
  allUVars :: Traversal' b u

class Monad m => MonadUnify e w u m | m -> w u e where
  unconstrained :: w -> m (UVar w u)
  solveUnification :: m b -> m (UnificationResult e w u b)
  reflectCollectedConstraints :: m (M.Map (UVar w u) u)

  (-?=) :: (Partial w u, Unifiable w u e m u) => (UVar w u) -> u -> m ()

infix 4 =?=

class Monad m => MonadUnificationExcept e w u m | m -> e w u where
  throwUnificationFailure :: UnificationFailure e w u -> m a

-- | Types @b@ that are unifiable with by solving for UVars that stand for
-- their @u@ subterms
class (MonadUnificationExcept e w u m, HasUVars u b)
      => Unifiable w u e m b | m -> u w e where
  -- | traverse every unification variable in b.
  (=?=) :: b -> b -> m ()

class MonadCheckpointUnification w u m | m -> u w where
  listenUnconstrainedUVars :: m a -> m (a, S.Set (UVar w u))

-- ----------------------------------------

-- prism helper functions
  
isUVar :: Partial w u => u -> Maybe (UVar w u)
isUVar t = t ^? _UVar

injectUVar :: Partial w u => UVar w u -> u
injectUVar v = v^.re _UVar

-- -------------------- instances

instance HasUVars u b => HasUVars u [b] where
  allUVars _f [] = pure []
  allUVars f (b:bs) = (:) <$> allUVars f b <*> allUVars f bs

instance Functor m => Functor (UnificationT w u m) where
  fmap f = UnificationT . fmap f . ificationT

instance (Functor m, Monad m) => Applicative (UnificationT w u m) where
  pure = UnificationT . pure
  umf <*> umx = UnificationT (ificationT umf <*> ificationT umx)

instance Monad m => Monad (UnificationT w u m) where
  return = UnificationT . return
  umx >>= umf = UnificationT $ 
    ificationT umx >>= \ x -> ificationT (umf x)

instance U.LFresh m => U.LFresh (UnificationT w u m) where
  lfresh = UnificationT . U.lfresh
  avoid ns = UnificationT . U.avoid ns . ificationT
  getAvoids = UnificationT U.getAvoids

instance MonadTrans (UnificationT w u) where
  lift = UnificationT . lift

instance Reader.MonadReader r m => Reader.MonadReader r (UnificationT w u m) where
  ask = UnificationT Reader.ask
  local f = UnificationT . Reader.local f . ificationT
  reader = UnificationT . Reader.reader

instance Error.MonadError e m => Error.MonadError e (UnificationT w u m) where
  throwError = UnificationT . Error.throwError
  catchError uma handler = UnificationT (ificationT uma
                                         `Error.catchError`
                                         (ificationT . handler))

instance (MonadUnificationExcept e w u m)
         => MonadUnificationExcept e w u (UnificationT w u m) where
  throwUnificationFailure = UnificationT . lift . throwUnificationFailure

instance (Monad m, Partial w u, MonadUnificationExcept e w u (UnificationT w u m))
         => MonadUnify e w u (UnificationT w u m) where
  unconstrained = instUnconstrained
  reflectCollectedConstraints = UnificationT $ summarizeConstraints
  solveUnification = instSolveUnification
  (-?=) = addConstraintUVar

instance Monad m => MonadCheckpointUnification w u (UnificationT w u m) where
  -- listenUnconstrainedUVars :: m a -> m (a, S.Set (UVar u))
  listenUnconstrainedUVars comp = do
    let allKnownUVars = UnificationT $ uses (equivalenceClasses.equivReps) M.keys
        representatives us = do
          rus <- mapM represent us
          return $ S.fromList rus
    usInit <- allKnownUVars
    x <- comp
    usFinal <- allKnownUVars
    rusInit <- representatives usInit
    rusFinal <- representatives usFinal
    cs <- UnificationT $ use collectedConstraints
    let newRus = rusFinal S.\\ rusInit
        freshUs = S.mapMonotonic canonicalRep $ S.filter (not . flip M.member cs) newRus
    return (x, freshUs)

-- if we ever need to delay solving some constraints, this would be
-- the place to force them.
instSolveUnification :: Monad m => UnificationT w u m b -> UnificationT w u m (UnificationResult e w u b)
instSolveUnification comp = liftM UOkay comp

                            
instUnconstrained :: Monad m => w -> UnificationT w u m (UVar w u)
instUnconstrained klass = do
  j <- UnificationT $ nextFreshId <<%= (+1)
  let u = UVar j klass
  _ <- represent u
  return u

represent :: Monad m => UVar w u -> UnificationT w u m (Rep (UVar w u))
represent u = UnificationT $ do
  eqc <- use equivalenceClasses
  let r_ = representative' u eqc
  case r_ of
   Just r -> return r
   Nothing -> do
     let r = Rep u
     (equivalenceClasses . equivReps) %= M.insert u r
     (equivalenceClasses . equivSiblings) %= M.insert r (S.singleton u)
     return r

addConstraintUVar :: (Partial w u, Unifiable w u e (UnificationT w u m) u,
                      Monad m,
                      MonadUnificationExcept e w u (UnificationT w u m))
                     => UVar w u -> u -> UnificationT w u m ()
addConstraintUVar v t_ = do
  t <- applyCurrentSubstitution t_
  occursCheck v t
  -- first see if there's already a constraint on v and
  -- try to unify it with the given constraint
  t2 <- applyCurrentSubstitution (injectUVar v)
  case isUVar t2 of
    Just v' | v == v' -> return ()
            | otherwise -> UnificationT $ equivalenceClasses %= unite v v'
    _ -> t =?= t2
  -- then check if the given constraint is a simple uvar or a proper constraint
  -- and update the collectd constraints or the equivalence classes.
  t' <- applyCurrentSubstitution t
  case t'^?_UVar of
   Nothing -> do
     r <- represent v
     UnificationT $ collectedConstraints . at r ?= t'
   Just v'' -> UnificationT $ equivalenceClasses %= unite v v''

applyCurrentSubstitution :: (Partial w u, Unifiable w u e (UnificationT w u m) u, Monad m)
                            => u -> UnificationT w u m u
applyCurrentSubstitution = mapMOf allUVars replace
  where
    replace :: (Partial w u, Unifiable w u e (UnificationT w u m) u, Monad m)
               => u -> UnificationT w u m u
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
      
occursCheck :: forall w u e m .
               (Partial w u, Monad m,
                Unifiable w u e (UnificationT w u m) u,
                MonadUnificationExcept e w u (UnificationT w u m))
               => UVar w u -> u -> UnificationT w u m ()
occursCheck v t = do
  r <- represent v
  let
    isV :: u -> UnificationT w u m Bool
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
evalUnificationT :: Monad m => UnificationT w u m a -> m a
evalUnificationT comp =
  St.evalStateT (ificationT comp) initialS

-- | Run the unification monad transformer and return the computation result
-- and the final map of constraints.
runUnificationT :: (Partial w u, Monad m) => UnificationT w u m a -> m (a, M.Map (UVar w u) u)
runUnificationT comp =
  let stcomp = do
        a <- ificationT comp
        m <- summarizeConstraints
        return (a, m)
  in St.evalStateT stcomp initialS

summarizeConstraints :: (Partial w u, MonadState (S w u) m) => m (M.Map (UVar w u) u)
summarizeConstraints = do
  mc_ <- use collectedConstraints
  mr_ <- use (equivalenceClasses . equivReps)
  let
    mc = M.mapKeysMonotonic canonicalRep mc_
    mr = fmap (injectUVar . canonicalRep) mr_
  return $ M.union mc mr -- prefer constraints to reps


initialS :: S w u
initialS =
  S {
    _nextFreshId = 0
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
      in eqs & equivReps %~ (appEndo $ mconcat $ map (\w -> Endo (M.insert w canonical)) $ S.toList others)
         & equivSiblings %~ (M.insert canonical (S.union (representedBy canonical eqs) others)
                             . M.delete other)

representedBy :: Ord a => (Rep a) -> EquivalenceClass a -> S.Set a
representedBy r eqs =
  fromMaybe S.empty $ M.lookup r (eqs^.equivSiblings)

representative :: Ord a => a -> EquivalenceClass a -> (Rep a)
representative x = fromMaybe (Rep x) . representative' x

representative' :: Ord a => a -> EquivalenceClass a -> Maybe (Rep a)
representative' x eqs = M.lookup x (eqs^.equivReps)

isSingletonEquivalenceClass :: Ord a => EquivalenceClass a -> a -> Bool
isSingletonEquivalenceClass eqs x =
  let r = representative x eqs
      sibs = eqs^. equivSiblings . at r
  in
   case sibs of
    Just s -> S.size s == 1
    Nothing -> False
