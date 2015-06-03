{-# LANGUAGE FlexibleContexts #-}
module Insomnia.ToF.Type where

import Control.Lens
import Control.Monad.Reader
import Data.Monoid
import qualified Data.Map as M

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.ToF.Env

typeAlias :: ToF m => TypeAlias -> m F.SemanticSig
typeAlias (ManifestTypeAlias bnd) =
  U.lunbind bnd $ \(tvks, t) ->
  withTyVars tvks $ \tvks' -> do
    (t', kcod) <- type' t
    let kdoms = map snd tvks'
        k = kdoms `F.kArrs` kcod
    return $ F.TypeSem t' k
typeAlias (DataCopyTypeAlias _tp _defn) =
  error "internal error: ToF.Type.typeAlias - translation of datatype copies unimplemented"

withTyVars :: ToF m => [KindedTVar] -> ([(F.TyVar, F.Kind)] -> m r) -> m r
withTyVars [] kont = kont []
withTyVars (tvk:tvks) kont =
  withTyVar tvk $ \tvk' -> 
  withTyVars tvks $ \tvks' ->
  kont $ tvk':tvks'

withTyVar :: ToF m => KindedTVar -> ((F.TyVar, F.Kind) -> m r) -> m r
withTyVar (tv, k) kont = do
  k' <- kind k
  withFreshName (U.name2String tv) $ \tv' -> 
    local (tyVarEnv %~ M.insert tv (tv', k'))
    $ kont $ (tv', k')

kind :: Monad m => Kind -> m F.Kind
kind KType = return F.KType
kind (KArr k1 k2) = do
  k1' <- kind k1
  k2' <- kind k2
  return $ F.KArr k1' k2'

type' :: ToF m => Type -> m (F.Type, F.Kind)
type' t_ =
  case t_ of
   TV tv -> do
     mv <- view (tyVarEnv . at tv)
     case mv of
      Just (tv', k') -> return (F.TV tv', k')
      Nothing -> do
        env <- view tyVarEnv
        env' <- view valEnv
        throwError ("ToF.type' internal error: type variable " <> show tv
                    <> " not in environment " <> show env
                    <> " and value env " <> show env')
   TUVar u -> throwError ("ToF.type' internal error: unexpected unification variable " ++ show u)
   TC tc -> typeConstructor tc
   TAnn t k -> do
     (t', _) <- type' t
     k' <- kind k
     return (t', k')
   TApp t1 t2 -> do
     (t1', karr) <- type' t1
     (t2', _) <- type' t2
     case karr of
      (F.KArr _ k2) -> do
        -- do a bit of normalization if possible
        tarr <- betaWhnf (F.TApp t1' t2')
        return (tarr, k2)
      F.KType -> throwError "ToF.type' internal error: unexpected KType in function position of type application"
   TForall bnd ->
     U.lunbind bnd $ \((tv, k), tbody) -> 
     withTyVar (tv,k) $ \(tv', k') -> do
       (tbody', _) <- type' tbody
       let
         tall = F.TForall $ U.bind (tv', U.embed k') $ tbody'
       return (tall, F.KType)
   TRecord (Row lts) -> do
     fts <- forM lts $ \(l, t) -> do
       (t', _) <- type' t
       return (F.FUser $ labelName l, t')
     return (F.TRecord fts, F.KType)

-- opportunistically beta reduce some types.
betaWhnf :: U.LFresh m => F.Type -> m F.Type
betaWhnf t_ =
  case t_ of
   F.TApp t1 t2 -> do
     t1' <- betaWhnf t1
     case t1' of
      F.TLam bnd -> 
        U.lunbind bnd $ \((tv,_k), tB) ->
        betaWhnf (U.subst tv t2 tB)
      _ -> return $ F.TApp t1' t2
   _ -> return $ t_
     
   

typeConstructor :: ToF m => TypeConstructor -> m (F.Type, F.Kind)
typeConstructor (TCLocal tc) = do
  ma <- view (tyConEnv . at tc)
  e <- view tyConEnv
  case ma of
   Just (F.TypeSem t k) -> return (t, k)
   Just (F.DataSem d _ k) -> return (F.TV d, k)
   Just f -> throwError $ "ToF.typeConstructor: wanted a TypeSem, got a " ++ show f
   Nothing -> throwError $ "ToF.typeConstructor: tyConEnv did not contain a TypeSem for a local type constructor: " ++ show tc ++ " in " ++ show e
typeConstructor (TCGlobal (TypePath p f)) = do
  let
    findIt ident = do
      ma <- view (modEnv . at ident)
      case ma of
       Just (sig, x) -> return (sig, F.V x)
       Nothing -> throwError "ToF.typeConstructor: type path has unbound module identifier at the root"
  (s, _m) <- followUserPathAnything findIt (ProjP p f)
  case s of
   F.TypeSem t k -> return (t, k)
   F.DataSem d _ k -> return (F.TV d, k)
   _ -> throwError "ToF.typeConstructor: type path maps to non-type semantic signature"
  
