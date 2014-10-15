-- | This is just an exception monad like ErrorT from transformers-0.3.0.0
-- except that it doesn't require the error type to be an instance of Error.
-- (so it's like ExceptT from transformers-0.4.0.0)
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module Insomnia.Except where

import Control.Applicative

import Data.Foldable (Foldable(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (Monoid(..))
import Data.Traversable (Traversable(..))

import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class

import Control.Monad.Error.Class

newtype ExceptT e m a = ExceptT { runExceptT :: m (Either e a) }

instance (Functor m) => Functor (ExceptT e m) where
    fmap f = ExceptT . fmap (fmap f) . runExceptT

instance (Foldable f) => Foldable (ExceptT e f) where
    foldMap f (ExceptT a) = foldMap (either (const mempty) f) a

instance (Traversable f) => Traversable (ExceptT e f) where
    traverse f (ExceptT a) =
        ExceptT <$> traverse (either (pure . Left) (fmap Right . f)) a

instance (Functor m, Monad m) => Applicative (ExceptT e m) where
    pure a = ExceptT $ return (Right a)
    ExceptT f <*> ExceptT v = ExceptT $ do
        mf <- f
        case mf of
            Left e -> return (Left e)
            Right k -> do
                mv <- v
                case mv of
                    Left e -> return (Left e)
                    Right x -> return (Right (k x))

instance (Functor m, Monad m, Monoid e) => Alternative (ExceptT e m) where
    empty = mzero
    (<|>) = mplus

instance (Monad m) => Monad (ExceptT e m) where
    return a = ExceptT $ return (Right a)
    m >>= k = ExceptT $ do
        a <- runExceptT m
        case a of
            Left e -> return (Left e)
            Right x -> runExceptT (k x)
    fail = ExceptT . fail

instance (Monad m, Monoid e) => MonadPlus (ExceptT e m) where
    mzero = ExceptT $ return (Left mempty)
    ExceptT m `mplus` ExceptT n = ExceptT $ do
        a <- m
        case a of
            Left e -> liftM (either (Left . mappend e) Right) n
            Right x -> return (Right x)

instance (MonadFix m) => MonadFix (ExceptT e m) where
    mfix f = ExceptT $ mfix $ \ a -> runExceptT $ f $ case a of
        Right x -> x
        Left _ -> error "mfix ExceptT: Left"

instance MonadTrans (ExceptT e) where
    lift = ExceptT . liftM Right

instance (MonadIO m) => MonadIO (ExceptT e m) where
    liftIO = lift . liftIO                                  

instance Monad m => MonadError e (ExceptT e m) where
  throwError = ExceptT . return . Left
  m `catchError` h = ExceptT $ do
    a <- runExceptT m
    case a of
      Left l -> runExceptT (h l)
      Right r -> return (Right r)

type Except e = ExceptT e Identity

runExcept :: Except e a -> Either e a
runExcept = runIdentity . runExceptT
