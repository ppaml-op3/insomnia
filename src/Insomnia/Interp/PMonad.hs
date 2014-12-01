{-# LANGUAGE RankNTypes #-}
module Insomnia.Interp.PMonad (ProbabilityMonad(..)
                              , SupportMonad(..)
                              , ExpMonad(..)
                              , SamplingMonad(..)
                              , ContinuousProbabilityMonad(..)
                              , samples
                              , ConditioningMonad(..)
                              , Exp
                              , Support
                              , Sample
                              , probability
                              , certainty
                              , impossibility
                              , logOdds)
       where

import Control.Applicative
import Control.Monad ()
import System.Random (RandomGen(split), random, newStdGen)

type Probability = Double    -- number from 0 to 1
certainty, impossibility :: Probability
certainty = 1.0
impossibility = 0.0

probability :: ExpMonad m => (a -> Bool) -> m a -> Double
probability p = expectation (numOfBool . p)
  where numOfBool True = certainty
        numOfBool False = impossibility

logOdds :: ExpMonad m => (a -> Bool) -> m a -> Double
logOdds p dist =
  10 * (logBase 10 (probability p dist) - logBase 10 (probability (not . p) dist))

class Monad m => ProbabilityMonad m where
    choose :: Probability -> m a -> m a -> m a
class ProbabilityMonad m => SupportMonad m where
  support :: m a -> [a]
  -- support (return x) = [x]
  -- support (d >>= k) = 
  --   concat [support (k x) | x <- support d]
  -- support (choose p d d') = 
  --   support d ++ support d'
class ProbabilityMonad m => ExpMonad m where
  expectation :: (a -> Double) -> m a -> Double
  -- expectation h (return x) = h x
  -- expectation h (d >>= k)  = expectation g d 
  --          where g x = expectation h (k x)
  -- expectation h (choose p d d') =
  --      p * expectation h d +
  --        (1-p) * expectation h d'
  -- sample (return x) r = (x, r)
  -- sample (d >>= k)  r = 
  --   let (x, r') = sample d r in sample (k x) r'
  -- sample (choose p d d') r = 
  --   if r < p then sample d (r/p) 
  --   else sample d' ((1-r)/(1-p))
class ProbabilityMonad m => SamplingMonad m where
  sample :: RandomGen g => m a -> g -> (a, g)
  -- sample (return x) g = (x, g)
  -- sample (d >>= k)  g = 
  --   let (x, g') = sample d g in sample (k x) g'
  -- sample (choose p d d') g =
  --   let (x, g') = random g in
  --     sample (if x < p then d else d') g'
newtype Support a = Support [a]
instance Functor Support where
  fmap f (Support l) = Support (fmap f l)
instance Applicative Support where
  pure = return
  (Support lf) <*> (Support lx) =
    Support [f x | f <- lf , x <- lx]
instance Monad Support where
  return x = Support [x]
  (Support l) >>= k =
    Support (concat [s | x <- l, let Support s = k x])
instance ProbabilityMonad Support where
  choose _ (Support l) (Support l') = Support (l ++ l')
instance SupportMonad Support where
  support (Support l) = l
newtype Exp a = Exp ((a -> Double) -> Double)
instance Functor Exp where
  fmap f (Exp d) = Exp (\h -> d (h . f))
instance Applicative Exp where
  pure = return
  (Exp df) <*> (Exp dx) = Exp (\h -> df (\f -> dx (\x -> h (f x))))
instance Monad Exp where
  return x = Exp (\h -> h x)
  (Exp d) >>= k = 
     Exp (\h -> let apply (Exp f) arg = f arg
                    g x = apply (k x) h
                in  d g)
instance ProbabilityMonad Exp where
  choose p (Exp d1) (Exp d2) = 
    Exp (\h -> p * d1 h + (1-p) * d2 h)
instance ExpMonad Exp where
  expectation h (Exp d) = d h
newtype Sample a = Sample (forall g . RandomGen g => g -> (a, g))
instance Functor Sample where
  fmap f (Sample s) = Sample (\g -> let (x, g') = s g
                                    in (f x, g'))
instance Applicative Sample where
  pure = return
  (Sample sf) <*> (Sample sx) =
    Sample (\g -> let
               (g1, g2) = split g
               (f, _) = sf g1
               (x, g'') = sx g2
               in (f x, g''))
instance Monad Sample where
  return x = Sample (\ g -> (x, g))
  (Sample s) >>= k = 
      Sample (\ g -> let (a, g')   = s g
                         Sample s' = k a
                     in  s' g')
instance ProbabilityMonad Sample where
  choose p (Sample s1) (Sample s2) = 
    Sample (\g -> let (x, g') = random g
                  in  (if x < p then s1 else s2) g')
instance SamplingMonad Sample where
  sample (Sample s) g = s g

class ProbabilityMonad m => ContinuousProbabilityMonad m where
  u :: m Probability -- uniform over the unit interval

instance ContinuousProbabilityMonad Sample where
  u = Sample random


samples :: SamplingMonad m => m a -> IO [a]
samples m =
  do gen <- newStdGen
     return $ run gen
  where run g = let (a, g') = sample m g in a : run g'
        
class ProbabilityMonad m => ConditioningMonad m where
  pfilter :: (a -> Bool) -> m a -> m a

instance ConditioningMonad Sample where
  -- conditioning implemented by rejection sampling
  pfilter p (Sample s) = Sample s'
    where s' g = let (a, g') = s g
                 in if p a then (a, g')
                    else s' g'

instance ConditioningMonad Exp where
  pfilter p (Exp integrate) = Exp integrate'
    where integrate' f = integrate (\a -> if p a then f a else 0) /
                         integrate (\a -> if p a then 1 else 0)
                        


instance ConditioningMonad Support where
  pfilter p (Support as) = Support (filter p as)
