{-# OPTIONS_GHC -fno-warn-orphans #-}
module Insomnia.SurfaceSyntax.ExtraInstances where

import Control.Monad.Morph
import qualified Control.Monad.Except as Ex

import Unbound.Generics.LocallyNameless.Fresh

import Pipes.Core
import Pipes.Lift (distribute)
  
instance MFunctor FreshMT where
  hoist f = FreshMT . hoist f . unFreshMT

runFreshMP :: Monad m => Proxy a' a b' b (FreshMT m) r -> Proxy a' a b' b m r
runFreshMP = runFreshMT . distribute

runExceptP :: Monad m => Proxy a' a b' b (Ex.ExceptT e m) r -> Proxy a' a b' b m (Either e r)
runExceptP = Ex.runExceptT . distribute

instance Fresh m => Fresh (Proxy a' a b' b m) where
  fresh = lift . fresh
