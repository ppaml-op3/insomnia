-- | The "to AST" monad.
--
{-# LANGUAGE RankNTypes,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TemplateHaskell
  #-}
module Insomnia.SurfaceSyntax.ToastMonad (
  -- * Translation Context
  Ctx(..)
  , declaredFixity
  , currentModuleKind
    -- * Translation monads
  , TA
  , YTA
  , CTA (..)
    -- * Suspended computation state
  , Suspended
  , ImportFileError (..)
  , feedTA
  , await
  , freshTopRef
  , withTopRefFor_
  , tellToplevel
  , listenToplevels
    -- * Monad stacks
  , liftCTA
  , runToAST
  , module Control.Monad.Reader.Class
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.Reader.Class
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.State

import qualified Data.Map as M
import Data.Monoid

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind

import qualified Insomnia.Identifier as I
import qualified Insomnia.Toplevel as I

import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.FixityParser

data Ctx = Ctx {_declaredFixity :: M.Map QualifiedIdent Fixity
               , _currentModuleKind :: ModuleKind
               }
         deriving (Show)

$(makeLenses ''Ctx)

data ToastState =
  ToastState { _toprefMapSt :: M.Map FilePath I.TopRef
             , _toprefAccumSt :: Endo [(FilePath, I.TopRef, I.Toplevel)]
             }

$(makeLenses ''ToastState)

instance Monoid ToastState where
  mempty = ToastState mempty mempty
  (ToastState a b) `mappend` (ToastState a' b') = ToastState (a <> a') (b <> b')

-- "To AST" monad is just a reader of some contextual info...
-- (the freshness monad is used to make new Toprefs)
type TA = ReaderT Ctx (StateT ToastState (U.FreshMT YTA))

-- ... except that we can yield mid-computation and ask for an imported file.
--
-- this is a coroutine monad.
data YTA a = 
  DoneTA a
  | YieldTA Suspended ImportFileSpec (Either ImportFileError Toplevel -> TA a)

type Suspended = (Ctx, ToastState, Integer)

newtype ImportFileError = ImportFileError { importFileErrorMsg :: String }

instance Functor YTA where
  fmap f (DoneTA x) = DoneTA (f x)
  fmap f (YieldTA susp want k) = YieldTA susp want (fmap f . k)

instance Applicative YTA where
  pure = DoneTA 
  (DoneTA f) <*> (DoneTA x) = DoneTA (f x)
  (DoneTA f) <*> (YieldTA susp want k) = YieldTA susp want (fmap f . k)
  (YieldTA susp want f) <*> m = YieldTA susp want (\i -> f i <*> (lift . lift . lift) m)

instance Monad YTA where
   return = pure
   DoneTA x >>= k = k x
   YieldTA susp want k >>= k' = YieldTA susp want (\i -> k i >>= (lift . lift . lift . k'))

-- the CPS version of TA
newtype CTA a = CTA { runCTA :: forall r . (a -> TA r) -> TA r }

instance Monad CTA where
  return x = CTA $ \k -> k x
  m >>= f = CTA $ \k -> runCTA m $ \x -> runCTA (f x) k

instance Applicative CTA where
  pure = return
  mf <*> mx = CTA $ \k -> runCTA mf $ \f -> runCTA mx $ \x -> k (f x)

instance Functor CTA where
  fmap f mx = CTA $ \k -> runCTA mx $ \x -> k (f x)

-- in the CPS version of TA, the Ctx is a state that persists
-- within the continuation.
instance MonadState Ctx CTA where
  state xform = CTA $ \k -> do
    ctx <- ask
    let (x, ctx') = xform ctx
    local (const ctx') $ k x

-- | given a To AST computation and a monadic handler for import requests and an initial context,
-- repeatedly call the handler whenever the To AST computation yields with a request until it returns a final answer.
-- Return that final answer.
feedTA :: forall m a .
          Monad m
          => TA a
          -> (ImportFileSpec -> m (Either ImportFileError Toplevel))
          -> Ctx -> m a
feedTA comp onImport =
  let
    go :: Suspended -> TA a -> m a
    go (ctx, st, freshness) c =
      case U.contFreshMT (evalStateT (runReaderT c ctx) st) freshness of
       DoneTA ans -> return ans
       YieldTA susp' wanted resume -> do
         reply <- onImport wanted
         go susp' (resume reply)
  in \ctx -> go (ctx, mempty, 0) comp

await :: ImportFileSpec -> TA Toplevel
await want = do
  ctx <- ask
  st <- lift get
  freshness <- lift $ lift (U.FreshMT get)
  lift $ lift $ lift (YieldTA (ctx,st, freshness) want $ \got ->
                       case got of
                       Left err -> fail (importFileErrorMsg err)
                       Right it -> return it)

tellToplevel :: FilePath -> I.TopRef -> I.Toplevel -> TA ()
tellToplevel fp tr tl =
  let e = Endo $ \l -> (fp, tr, tl) : l
  in lift (toprefAccumSt <>= e)

listenToplevels :: TA a -> TA (a, [I.ToplevelItem])
listenToplevels comp = do
  a <- comp
  e <- use toprefAccumSt
  let its = map (\(fp,tr,tl) -> I.ToplevelImported fp tr tl) $ appEndo e []
  return (a, its)

-- | If the given 'FilePath' has a 'I.TopRef' associated with it,
-- just return it.  Otherwise, run the given computation passing it a
-- fresh 'I.TopRef', and then return the result
withTopRefFor_ :: FilePath -> (I.TopRef -> TA ()) -> TA I.TopRef
withTopRefFor_ fp compNew = do
  mref <- use (toprefMapSt . at fp)
  case mref of
   Nothing -> do
     a <- freshTopRef fp
     toprefMapSt . at fp ?= a
     compNew a
     return a
   Just a -> return a

freshTopRef :: FilePath -> TA I.TopRef
freshTopRef fp = U.fresh (U.s2n $ "^" ++ fp)

liftCTA :: TA a -> CTA a
liftCTA comp = CTA $ \k -> comp >>= k

runToAST :: Ctx -> TA a -> YTA a
runToAST ctx comp = U.runFreshMT (evalStateT (runReaderT comp ctx) mempty)

