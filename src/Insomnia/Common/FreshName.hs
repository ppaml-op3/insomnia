module Insomnia.Common.FreshName where


import Data.Typeable (Typeable)

import Unbound.Generics.LocallyNameless



withFreshName :: (Typeable a, LFresh m) => String -> (Name a -> m r) -> m r
withFreshName s kont = do
  n' <- lfresh $ s2n s
  avoid [AnyName n'] $ kont n'

withFreshNames :: (Typeable a, LFresh m) => [String]
                  -> ([Name a] -> m r) -> m r
withFreshNames [] kont = kont []
withFreshNames (s:ss) kont =
  withFreshName s $ \x ->
  withFreshNames ss $ \xs ->
  kont (x:xs)
