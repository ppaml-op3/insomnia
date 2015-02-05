{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses
  #-}
module FOmega.SemanticSig where

import Control.Monad (forM)
import Data.Typeable(Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless (Bind, Embed, Alpha, Subst, LFresh)
import qualified Unbound.Generics.LocallyNameless as U

import FOmega.Syntax

-- Σ
data SemanticSig =
  -- [τ]
  ValSem !Type
  -- [= τ:κ]
  | TypeSem !Type !Kind
  -- [= Ξ] -- We don't (yet) have nested signature definitions in
  -- Insomnia, so this is not entirely necessary.
  | SigSem !AbstractSig
  -- [= σ:κ]
  | DataSem !Type !Kind
  -- [∀β1...βM . τ1 → ... → τN → σ]
  | ConSem !Type
  -- { f1 = Σ1, ..., fn = Σn }
  | ModSem ![(Field, SemanticSig)]
    -- ∀ α1:κ1 ... αN:κN . Σ → Ξ
  | FunctorSem !(Bind [(TyVar, Embed Kind)] SemanticFunctor)
    deriving (Show, Typeable, Generic)

data SemanticFunctor =
  -- Σ → Ξ
  SemanticFunctor !SemanticSig !AbstractSig
  deriving (Show, Typeable, Generic)

-- Ξ
newtype AbstractSig =
  -- ∃ α1:κ1 ... αN:κN . Σ
  AbstractSig (Bind [(TyVar, Embed Kind)] SemanticSig)
  deriving (Show, Typeable, Generic)

instance Alpha SemanticSig
instance Alpha SemanticFunctor
instance Alpha AbstractSig

instance Subst Type SemanticSig
instance Subst Type SemanticFunctor
instance Subst Type AbstractSig

-- * Embedding into F Omega
-- 
-- The "F-ing Modules" paper shows that semantic signatures can be embedded into plain vanilla FΩ.
--

embedSemanticSig :: LFresh m => SemanticSig -> m Type
embedSemanticSig (ValSem t) = return $ TRecord [(FVal, t)]
embedSemanticSig (TypeSem t k) = do
  -- this is slightly tricky because we want to embed a higher-kinded
  -- constructor t of kind k into KType.  We don't care about the
  -- particulars of the embedding as long as we have something of kind
  -- KType that is inhabited whenever t is well-formed.  So we use the
  -- type of an identity function of argument (α t) where α is of kind
  -- k→KType.
  a <- U.lfresh $ U.s2n "α"
  let
    tConsume = TApp (TV a) t
    tEmbed = TForall $ U.bind (a, U.embed $ k `KArr` KType) $ TArr tConsume tConsume
  return $ TRecord [(FType, tEmbed)]
embedSemanticSig (SigSem absSig) = do
  s <- embedAbstractSig absSig
  return $ TRecord [(FSig, s)]
embedSemanticSig (DataSem t k) = do
  -- DataSem and ConSem are assumed to already be inside a record with distinguished fields, so
  -- no extra layer of record wrapping.
  a <- U.lfresh $ U.s2n "δ"
  let
    tConsume = TApp (TV a) t
    tEmbed = TForall $ U.bind (a, U.embed $ k `KArr` KType) $ TArr tConsume tConsume
  return tEmbed
embedSemanticSig (ConSem t) =
  return t
embedSemanticSig (ModSem fas) = do
  fts <- forM fas $ \(f, s) -> do
    t <- embedSemanticSig s
    return (f, t)
  return $ TRecord fts
embedSemanticSig (FunctorSem bnd) =
  U.lunbind bnd $ \(tvks, SemanticFunctor dom cod) -> do
    domT <- embedSemanticSig dom
    codT <- embedAbstractSig cod
    return $ closeForalls tvks $ TArr domT codT

embedAbstractSig :: LFresh m => AbstractSig -> m Type
embedAbstractSig (AbstractSig bnd) =
  U.lunbind bnd $ \(tvks, sig) -> do
    t <- embedSemanticSig sig
    return $ closeExistentials tvks t

closeForalls :: [(TyVar, Embed Kind)] -> Type -> Type
closeForalls [] = id
closeForalls (ak:aks) =
  TExist . U.bind ak . closeExistentials aks

closeExistentials :: [(TyVar, Embed Kind)] -> Type -> Type
closeExistentials [] = id
closeExistentials (ak:aks) =
  TExist . U.bind ak . closeExistentials aks
