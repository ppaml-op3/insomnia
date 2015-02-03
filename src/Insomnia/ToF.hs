{-# LANGUAGE ViewPatterns, TemplateHaskell, FlexibleContexts #-}
module Insomnia.ToF where

import Control.Lens
import Control.Monad.Reader
import Data.Monoid (Monoid(..), (<>))
import Data.Typeable (Typeable)
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh, Embed)
import qualified Unbound.Generics.LocallyNameless as U

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.Common.ModuleKind
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModuleType

data Env = Env { _tyConEnv :: M.Map TyConName F.SemanticSig
               , _tyVarEnv :: M.Map TyVar (F.TyVar, F.Kind)
               }

$(makeLenses ''Env)

class (Functor m, LFresh m, MonadReader Env m) => ToF m

moduleType :: ToF m => ModuleType -> m F.AbstractSig
moduleType modTy_ =
  case modTy_ of
   SigMT (SigV s ModuleMK) ->
     signature s

signature :: ToF m => Signature -> m F.AbstractSig
signature = fmap (uncurry mkAbstractModuleSig) . signature'
  where
    mkAbstractModuleSig :: [(F.TyVar, Embed F.Kind)]
                           -> [(F.Field, F.SemanticSig)]
                           -> F.AbstractSig
    mkAbstractModuleSig tvks =
      F.AbstractSig . U.bind tvks . F.ModSem

    signature' :: ToF m => Signature -> m ([(F.TyVar, Embed F.Kind)], [(F.Field, F.SemanticSig)])
    signature' UnitSig = return mempty
    signature' (ValueSig f t rest) = do
      (t', _) <- type' t
      let s = ([], [(F.FUser f, F.ValSem t')])
      rest' <- signature' rest
      return $ s <> rest'
    signature' (TypeSig f bnd) =
      U.lunbind bnd $ \((con, U.unembed -> tsd), rest) -> do
        case tsd of
         AliasTypeSigDecl alias -> do
           sig <- typeAlias alias
           rest' <- local (tyConEnv %~ M.insert con sig) $ signature' rest
           let
             s = ([], [(F.FUser f, sig)])
           return $ s <> rest'
         AbstractTypeSigDecl k ->
           withFreshName con $ \tv -> do
             k' <- kind k
             let sig = F.TypeSem (F.TV tv) k'
             rest' <- local (tyConEnv %~ M.insert con sig) $ signature' rest
             let
               s = ([(tv, U.embed k')], [(F.FUser f, sig)])
             return $ s <> rest'

typeAlias :: ToF m => TypeAlias -> m F.SemanticSig
typeAlias (TypeAlias bnd) =
  U.lunbind bnd $ \(tvks, t) ->
  withTyVars tvks $ \tvks' -> do
    (t', kcod) <- type' t
    let kdoms = map (U.unembed . snd) tvks'
        k = kdoms `F.kArrs` kcod
    return $ F.TypeSem t' k

withFreshName :: (Typeable a, Typeable b, ToF m) => U.Name a -> (U.Name b -> m r) -> m r
withFreshName n kont = do
  n' <- U.lfresh $ U.s2n $ U.name2String n
  U.avoid [U.AnyName n'] $ kont n'

withTyVars :: ToF m => [KindedTVar] -> ([(F.TyVar, Embed F.Kind)] -> m r) -> m r
withTyVars [] kont = kont []
withTyVars ((tv, k):tvks) kont = do
  k' <- kind k
  withFreshName tv $ \tv' -> 
    local (tyVarEnv %~ M.insert tv (tv', k'))
    $ withTyVars tvks
    $ \rest ->
       kont $ (tv', U.embed k') : rest

kind :: Monad m => Kind -> m F.Kind
kind KType = return F.KType
kind (KArr k1 k2) = do
  k1' <- kind k1
  k2' <- kind k2
  return $ F.KArr k1' k2'

type' :: ToF m => Type -> m (F.Type, F.Kind)
type' _ = fail "unimplemented ToF.type'"
