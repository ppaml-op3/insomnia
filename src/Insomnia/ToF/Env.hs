-- | 
{-# LANGUAGE TemplateHaskell,
      FlexibleContexts, FlexibleInstances, TypeSynonymInstances
 #-}
module Insomnia.ToF.Env (
  Insomnia.Common.FreshName.withFreshName
  , Insomnia.Common.FreshName.withFreshNames
  , Env(..)
  , tyConEnv
  , sigEnv
  , modEnv
  , tyVarEnv
  , valConEnv
  , valEnv
  , TermVarProvenance(..)
  , emptyToFEnv
  , ToFM
  , ToF (..)
  , runToFM
  , followUserPathAnything
  , Control.Monad.Except.throwError
       ) where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import qualified Data.List as List
import qualified Data.Map as M
import Data.Monoid

import qualified Unbound.Generics.LocallyNameless as U
import Unbound.Generics.LocallyNameless (LFresh)

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr (Var)
import Insomnia.TypeDefn (ValConName)

import Insomnia.Common.FreshName

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

-- | when we translate insomnia term variables, we keep track of
-- whether they came from a local binding or from a previous
-- definition in the current module.
data TermVarProvenance = LocalTermVar
                       | StructureTermVar !F.SemanticSig
                       deriving (Show)
  
data Env = Env { _tyConEnv :: M.Map TyConName F.SemanticSig
               , _sigEnv   :: M.Map SigIdentifier F.AbstractSig
               , _modEnv   :: M.Map Identifier (F.SemanticSig, F.Var)
               , _tyVarEnv :: M.Map TyVar (F.TyVar, F.Kind)
               , _valConEnv :: M.Map ValConName (F.Var, F.Field)
               , _valEnv    :: M.Map Var (F.Var, TermVarProvenance)
               }

$(makeLenses ''Env)

emptyToFEnv :: Env
emptyToFEnv = Env initialTyConEnv mempty mempty mempty mempty mempty

initialTyConEnv :: M.Map TyConName F.SemanticSig
initialTyConEnv = M.fromList [(U.s2n "->",
                               F.TypeSem arrowLam ([F.KType, F.KType] `F.kArrs` F.KType))
                             , (U.s2n "Dist", F.TypeSem distLam (F.KType `F.KArr` F.KType))
                             , (U.s2n "Real", F.TypeSem (F.TV $ U.s2n "Real") F.KType)
                             , (U.s2n "Int", F.TypeSem (F.TV $ U.s2n "Int") F.KType) 
                             ]
  where
    arrowLam = F.TLam $ U.bind (alpha, U.embed F.KType) $
               F.TLam $ U.bind (beta, U.embed F.KType) $
               F.TArr (F.TV alpha) (F.TV beta)
    distLam = F.TLam $ U.bind (alpha, U.embed F.KType) $ F.TDist (F.TV alpha)
    alpha = U.s2n "α"
    beta = U.s2n "β"

class (Functor m, LFresh m, MonadReader Env m, MonadError String m, MonadPlus m) => ToF m

type ToFM = ExceptT String (ReaderT Env U.LFreshM)

instance ToF ToFM

runToFM :: ToFM a -> a
runToFM m =
  case U.runLFreshM (runReaderT (runExceptT m) emptyToFEnv) of
   Left s -> error $ "unexpected failure in ToF.runToFM: “" ++ s ++ "”"
   Right a -> a

followUserPathAnything :: (MonadError String m) =>
                          (Identifier -> m (F.SemanticSig, F.Term))
                          -> Path -> m (F.SemanticSig, F.Term)
followUserPathAnything rootLookup (IdP ident) = rootLookup ident
followUserPathAnything rootLookup (ProjP path f) = do
  (mod1, m) <- followUserPathAnything rootLookup path
  case mod1 of
   (F.ModSem flds) -> do
     let p (F.FUser f', _) | f == f' = True
         p _ = False
     case List.find p flds of
      Just (_, mod2) -> return (mod2, F.Proj m (F.FUser f))
      Nothing -> throwError "unexpectd failure in followUserPathAnything: field not found"
   _ -> throwError "unexpected failure in followUserPathAnything: not a module record"
