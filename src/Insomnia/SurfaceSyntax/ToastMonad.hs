-- | The "to AST" monad.
--
{-# LANGUAGE RankNTypes,
      MultiParamTypeClasses,
      FlexibleContexts,
      ScopedTypeVariables,
      GeneralizedNewtypeDeriving,
      TemplateHaskell
  #-}
module Insomnia.SurfaceSyntax.ToastMonad (
  -- * Translation Context
  Ctx
  , makeCtxSimple
  , currentModuleKind
  , getDeclaredFixity
  , getDeclaredFixityC
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
  , updateWithFixity
  , updateWithFixityC
    -- * Translation monads
  , TA
  , CTA
  , runCTA
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
type TA m = ToastPipe (ToastStackT m)

-- we can request an ImportFileSpec and get a response of (Either ImportFileError Toplevel)
type ToastPipe = Pipes.Client ImportFileSpec (Either ImportFileError Toplevel)

type ToastStackBaseT m = ExceptT ToastError (U.FreshMT m)
-- this is the "normal" "to ast" monad stack where some information is contextual.
type ToastStackT m = ReaderT Ctx (StateT ToastState (ToastStackBaseT m))
-- this is the "incremental" "to ast" monad stack for situations where we need to statefully
-- build up the context  (for example if we're collecting information about names in a module).
type IncrToastStackT m = StateT (Ctx, ToastState) (ToastStackBaseT m)

data ToastError =
  ToastErrorMsg !String !(First SourcePos)

instance Show (ToastError) where
  showsPrec p (ToastErrorMsg msg (First Nothing)) = showsPrec p msg
  showsPrec _ (ToastErrorMsg msg (First (Just posn))) =
    prettySourcePos posn . showsPrec 0 msg

newtype ImportFileError = ImportFileError { importFileErrorMsg :: String }

-- the version of TA that assembles a Ctx incrementally (using state)
newtype CTA m a = CTA { unCTA :: ToastPipe (IncrToastStackT m) a }
                  deriving (Monad, Applicative, Functor, MonadError ToastError)

lowerCTA :: Monad m => CTA m a -> TA m a
lowerCTA comp =
  Pipes.Lift.readerP $ \ctx -> Pipes.Lift.stateP $ \s -> do
    (a, (_, s')) <- Pipes.Lift.runStateP (ctx, s) $ unCTA comp
    return (a, s')

liftCTA :: Monad m => TA m a -> CTA m a
liftCTA comp = CTA $ Pipes.Lift.stateP $ \(ctx, s) -> do
  (a, s') <- Pipes.Lift.runStateP s $ Pipes.Lift.runReaderP ctx comp
  return (a, (ctx, s'))

-- | Run the given CTA subcomputation, but restrict all changes to the 'Ctx' to
-- the extent of the given subcomputation.
scopeCTA :: Monad m => CTA m a -> CTA m a
scopeCTA = liftCTA . lowerCTA


runCTA :: Monad m => CTA m a -> TA m a
runCTA = lowerCTA

-- | Construct a context from a list of predeclared infix operators
makeCtxSimple :: [(QualifiedIdent, Fixity)] -> Ctx
makeCtxSimple fixities = Ctx (M.fromList fixities) ModuleMK mempty mempty

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
    handler c = do
      x <- c
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
withTopRefFor_ fp onNew =  allocTopRef (toprefMapSt) fp onNew

withTopRefForC_ :: Monad m => FilePath -> (I.TopRef -> CTA m ()) -> CTA m I.TopRef
withTopRefForC_ fp onNew = CTA $ allocTopRef (_2 . toprefMapSt) fp (unCTA . onNew)

-- | Check whether the state has a topref for the given filepath and allocate if it doesn't.
-- Just return the existing value, or run the 'onNew' computation if
-- new return @Left existing@ or @Right newlyAllocated@
allocTopRef :: forall st m .
               (U.Fresh m, MonadState st m)
               => ALens' st (M.Map FilePath I.TopRef)
               -> FilePath
               -> (I.TopRef -> m ())
               -> m I.TopRef
allocTopRef topRefMap fp onNew = do
  let
    l :: Lens' st (Maybe I.TopRef)
    l = (cloneLens topRefMap . at fp)
  mref <- use l
  case mref of
    Nothing -> do
      a <- freshTopRef fp
      l ?= a
      onNew a
      return a
    Just a -> return a

freshTopRef :: U.Fresh m => FilePath -> m I.TopRef
freshTopRef fp = U.fresh (U.s2n $ "^" ++ fp)

updateWithFixity :: Monad m => QualifiedIdent -> Fixity -> TA m a -> TA m a
updateWithFixity qid f =
  local (declaredFixity . at qid ?~ f)

updateWithFixityC :: Monad m => QualifiedIdent -> Fixity -> CTA m ()
updateWithFixityC qid f =
  CTA $ _1 . declaredFixity . at qid ?= f

insertBigIdent :: Monad m => Ident -> BigIdentSort -> TA m a -> TA m a
insertBigIdent ident sort =
  local (bigIdentSort %~ M.insert ident sort)

insertBigIdentC :: Monad m => Ident -> BigIdentSort -> CTA m ()
insertBigIdentC ident sort =
  CTA $ _1 . bigIdentSort %= M.insert ident sort

addModuleVarC :: Monad m => Ident -> I.Identifier -> CTA m ()
addModuleVarC ident x =
  insertBigIdentC ident (StructureBIS x)

addModuleVar :: Monad m => Ident -> I.Identifier -> TA m a -> TA m a
addModuleVar ident x =
  insertBigIdent ident (StructureBIS x)

addSignatureVar :: Monad m => Ident -> I.SigIdentifier -> TA m a -> TA m a
addSignatureVar ident x =
  insertBigIdent ident (SignatureBIS x)

addSignatureVarC :: Monad m => Ident -> I.SigIdentifier -> CTA m ()
addSignatureVarC ident x =
  insertBigIdentC ident (SignatureBIS x)

lookupBigIdent :: Monad m => Ident -> TA m (Maybe BigIdentSort)
lookupBigIdent ident = view (bigIdentSort . at ident)

getDeclaredFixity :: Monad m => TA m (M.Map QualifiedIdent Fixity)
getDeclaredFixity = view declaredFixity

getDeclaredFixityC :: Monad m => CTA m (M.Map QualifiedIdent Fixity)
getDeclaredFixityC = CTA $ use (_1 . declaredFixity)

toastPositioned :: Monad m => (a -> TA m b) -> Positioned a -> TA m b
toastPositioned f p =
  local (currentNearbyPosition .~ (First $ Just $ view positionedSourcePos p)) $ f (view positioned p)

toastPositionedC :: Monad m => (a -> CTA m b) -> Positioned a -> CTA m b
toastPositionedC f p = CTA $ do
  oldPos <- _1 . currentNearbyPosition <<.= (First $ Just $ view positionedSourcePos p)
  x <- unCTA $ f (view positioned p)
  _1 . currentNearbyPosition .= oldPos
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
