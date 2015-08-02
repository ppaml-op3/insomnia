-- | The "to AST" monad.
--
{-# LANGUAGE RankNTypes,
      MultiParamTypeClasses,
      FlexibleContexts,
      ScopedTypeVariables,
      TemplateHaskell
  #-}
module Insomnia.SurfaceSyntax.ToastMonad (
  -- * Translation Context
  Ctx(..)
  , declaredFixity
  , currentModuleKind
  , toastPositioned
  , toastPositionedC
  , toastNear
    -- * Structure/Signature Name resolution
  , bigIdentSort
  , BigIdentSort(..)
  , addModuleVar
  , addModuleVarC
  , addSignatureVar
  , addSignatureVarC
  , lookupBigIdent
    -- * Translation monads
  , TA
  , CTA (..)
  , ToastError
  , throwToastError
  , throwToastErrorC
    -- * Suspended computation state
  , ImportFileError (..)
  , feedTA
  , await
  , freshTopRef
  , withTopRefFor_
  , withTopRefForC_
  , tellToplevel
  , listenToplevels
    -- * Monad stacks
  , liftCTA
  , scopeCTA
  , module Control.Monad.Reader.Class
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.Error.Class
import Control.Monad.Except
import Control.Monad.Reader.Class
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.State.Strict

import qualified Pipes.Core as Pipes
import qualified Pipes.Lift

import qualified Data.Map as M
import Data.Monoid

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind

import qualified Insomnia.Identifier as I
import qualified Insomnia.Toplevel as I

import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.SourcePos
import Insomnia.SurfaceSyntax.FixityParser

import Insomnia.SurfaceSyntax.ExtraInstances (runFreshMP, runExceptP)

-- | A "BigIdentSort" classifies "big" idents as to whether they stand
-- for signatures or structures.
data BigIdentSort =
  SignatureBIS I.SigIdentifier
  | StructureBIS I.Identifier
    deriving (Show)

data Ctx = Ctx {_declaredFixity :: M.Map QualifiedIdent Fixity
               , _currentModuleKind :: ModuleKind
               , _bigIdentSort :: M.Map Ident BigIdentSort
               , _currentNearbyPosition :: First SourcePos
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
-- and it may request that the upstream client import a file.
type TA m = Pipes.Client ImportFileSpec (Either ImportFileError Toplevel) (ToastStackT m)

type ToastStackT m = ReaderT Ctx (StateT ToastState (ExceptT ToastError (U.FreshMT m)))

data ToastError =
  ToastErrorMsg !String !(First SourcePos)

instance Show (ToastError) where
  showsPrec p (ToastErrorMsg msg (First Nothing)) = showsPrec p msg
  showsPrec _ (ToastErrorMsg msg (First (Just posn))) =
    showsPrec 0 posn . showString ": " . showsPrec 0 msg

newtype ImportFileError = ImportFileError { importFileErrorMsg :: String }

-- the CPS version of TA
newtype CTA m a = CTA { runCTA :: forall r . (a -> TA m r) -> TA m r }

instance Monad (CTA m) where
  return x = CTA $ \k -> k x
  m >>= f = CTA $ \k -> runCTA m $ \x -> runCTA (f x) k

instance Applicative (CTA m) where
  pure = return
  mf <*> mx = CTA $ \k -> runCTA mf $ \f -> runCTA mx $ \x -> k (f x)

instance Functor (CTA m) where
  fmap f mx = CTA $ \k -> runCTA mx $ \x -> k (f x)

-- in the CPS version of TA, the Ctx is a state that persists
-- within the continuation.
instance Monad m => MonadState Ctx (CTA m) where
  state xform = CTA $ \k -> do
    ctx <- ask
    let (x, ctx') = xform ctx
    local (const ctx') $ k x

instance MonadError ToastError m => MonadError ToastError (CTA m) where
  throwError e = CTA $ \_k -> throwError e
  catchError comp handler = CTA $ \k -> do
    lOrR <- runCTA comp (return . Right) `catchError` (return . Left)
    case lOrR of
      Left err -> runCTA (handler err) k
      Right ans -> k ans

-- | given a To AST computation and a monadic handler for import requests and an initial context,
-- repeatedly call the handler whenever the To AST computation yields with a request until it returns a final answer.
-- Return that final answer.
feedTA :: forall m a .
          Monad m
          => TA m a
          -> (ToastError -> m a)
          -> (ImportFileSpec -> m (Either ImportFileError Toplevel))
          -> Ctx -> m a
feedTA comp onError onImport ctx =
  let
    compL = runFreshMP
            $ runExceptP 
            $ Pipes.Lift.evalStateP mempty
            $ Pipes.Lift.runReaderP ctx comp
    handler comp = do
      x <- comp
      case x of
        Right ans -> return ans
        Left err -> onError err
    -- TODO: run the handler inside the pipeline?  We don't really
    -- recover from errors, so it's not clear we'd gain anything.
  in handler $ Pipes.runEffect ( (lift . onImport) Pipes.>\\ compL)

await :: Monad m => ImportFileSpec -> TA m Toplevel
await spec = do
  ans <- Pipes.request spec
  case ans of
    Left err -> throwToastError $ importFileErrorMsg err
    Right ok -> return ok

tellToplevel :: Monad m => FilePath -> I.TopRef -> I.Toplevel -> TA m ()
tellToplevel fp tr tl =
   let e = Endo $ \l -> (fp, tr, tl) : l
   in lift (toprefAccumSt <>= e)

listenToplevels :: Monad m => TA m a -> TA m (a, [I.ToplevelItem])
listenToplevels comp = do
  a <- comp
  e <- use toprefAccumSt
  let its = map (\(fp,tr,tl) -> I.ToplevelImported fp tr tl) $ appEndo e []
  return (a, its)

-- | If the given 'FilePath' has a 'I.TopRef' associated with it,
-- just return it.  Otherwise, run the given computation passing it a
-- fresh 'I.TopRef', and then return the result
withTopRefFor_ :: Monad m => FilePath -> (I.TopRef -> TA m ()) -> TA m I.TopRef
withTopRefFor_ fp compNew = do
  mref <- use (toprefMapSt . at fp)
  case mref of
   Nothing -> do
     a <- freshTopRef fp
     toprefMapSt . at fp ?= a
     compNew a
     return a
   Just a -> return a

withTopRefForC_ :: Monad m => FilePath -> (I.TopRef -> CTA m ()) -> CTA m I.TopRef
withTopRefForC_ fp compNew =
  CTA $ \k -> do
    r <- withTopRefFor_ fp $ \r ->
      runCTA (compNew r) return
    k r

freshTopRef :: Monad m => FilePath -> TA m I.TopRef
freshTopRef fp = U.fresh (U.s2n $ "^" ++ fp)

liftCTA :: Monad m => TA m a -> CTA m a
liftCTA comp = CTA $ \k -> comp >>= k

-- | Run the given CTA subcomputation, but restrict all changes to the 'Ctx' to
-- the extent of the given subcomputation.
scopeCTA :: Monad m => CTA m a -> CTA m a
scopeCTA comp = liftCTA (runCTA comp return)

addModuleVarC :: Monad m => Ident -> I.Identifier -> CTA m ()
addModuleVarC ident x =
  CTA $ \k -> addModuleVar ident x (k ())

addModuleVar :: Monad m => Ident -> I.Identifier -> TA m a -> TA m a
addModuleVar ident x =
  insertBigIdent ident (StructureBIS x)

insertBigIdent :: Monad m => Ident -> BigIdentSort -> TA m a -> TA m a
insertBigIdent ident sort =
  local (bigIdentSort %~ M.insert ident sort)

addSignatureVar :: Monad m => Ident -> I.SigIdentifier -> TA m a -> TA m a
addSignatureVar ident x =
  insertBigIdent ident (SignatureBIS x)

addSignatureVarC :: Monad m => Ident -> I.SigIdentifier -> CTA m ()
addSignatureVarC ident x =
  CTA $ \k -> addSignatureVar ident x (k ())

lookupBigIdent :: Monad m => Ident -> TA m (Maybe BigIdentSort)
lookupBigIdent ident = view (bigIdentSort . at ident)

toastPositioned :: Monad m => (a -> TA m b) -> Positioned a -> TA m b
toastPositioned f p =
  local (currentNearbyPosition .~ (First $ Just $ view positionedSourcePos p)) $ f (view positioned p)

toastPositionedC :: Monad m => (a -> CTA m b) -> Positioned a -> CTA m b
toastPositionedC f p = do
  oldPos <- currentNearbyPosition <<.= (First $ Just $ view positionedSourcePos p)
  x <- f (view positioned p)
  currentNearbyPosition .= oldPos
  return x

throwToastError :: Monad m => String -> TA m a
throwToastError msg = do
  p <- view currentNearbyPosition
  throwError (ToastErrorMsg msg p)

throwToastErrorC :: Monad m => String -> CTA m a
throwToastErrorC = liftCTA . throwToastError

toastNear :: Monad m => Positioned s -> TA m a -> TA m a
toastNear p =
  local (currentNearbyPosition .~ (First $ Just $ view positionedSourcePos p))
