{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      FlexibleInstances, MultiParamTypeClasses,
      ScopedTypeVariables
  #-}
module Insomnia.Common.Telescope where

import Prelude hiding (mapM)

import Control.Applicative (Applicative(..), (<$>), Const(..))
import Control.Lens (mapMOf)
import qualified Control.Monad.Cont as Cont

import Data.Functor.Identity (Identity(..))
import Data.Monoid (Monoid)


import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Unbound.Generics.LocallyNameless

-- | A Telescope is a pattern that binds zero or more subpatterns such that
-- earlier members of the telescope scope over the remainder.
--
-- For example, Scheme's (let* ((v e) ...) body) may be represented by
-- @
--   data Expr = LetStar (Bind (Telescope Binding) Expr)
--   data Binding = Binding Var (Embed Expr)
--   type Var = Name Expr
-- @
data Telescope p =
  NilT
  | ConsT !(Rebind p (Telescope p))
  deriving (Show, Generic, Typeable)

instance Alpha p => Alpha (Telescope p)

instance Subst a p => Subst a (Telescope p)

-- | @Telescope p@ is almost an instance of 'Functor', except that @p@ and
-- @p'@ must be instances of 'Alpha'.
fmapTelescope :: (Alpha p, Alpha p') => (p -> p') -> Telescope p -> Telescope p'
fmapTelescope f = runIdentity . traverseTelescope (Identity . f)

-- | @Telescope p@ is almost an instance of 'Data.Foldable.Foldable', except that @p@ must
-- be an instance of 'Alpha'.
foldMapTelescope :: forall p m . (Alpha p, Monoid m) => (p -> m) -> Telescope p -> m
foldMapTelescope f = getConst . traverseTelescope (c . f)
  where
    c :: m -> Const m p
    c = Const

-- | @traverseTelescope :: (Alpha p, Alpha p') => Traversal (Telescope p) (Telescope p') p p'@
-- Not a 'Data.Traversable.Traversable' instance because of the constraints on @p@ and @p'@.
traverseTelescope :: (Alpha p, Alpha p', Applicative f) =>
                     (p -> f p') -> Telescope p -> f (Telescope p')
traverseTelescope _f NilT = pure NilT
traverseTelescope f (ConsT rbnd) = let
    consT x y = ConsT (rebind x y)
    (p, t) = unrebind rbnd
    in consT <$> f p <*> traverseTelescope f t

-- | Specialization of 'traverseTelescope' for CPS.
traverseTelescopeContT :: (Monad m, Alpha p, Alpha p') =>
                          (p -> (p' -> m r) -> m r) -> Telescope p -> (Telescope p' -> m r) -> m r
traverseTelescopeContT f t kont = Cont.runContT (mapMOf traverseTelescope (\p -> Cont.ContT (f p)) t) kont
