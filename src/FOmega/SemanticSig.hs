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
  -- [= σ = {f1:τ1 | … | fN:τN} : κ]
  | DataSem !Type !Type !Kind
  -- [∀β1...βM . τ1 → ... → τN → σ], the field is a hack to get to the
  -- associated data type.
  | ConSem !Type !Field 
  -- { f1 = Σ1, ..., fn = Σn }
  | ModSem ![(Field, SemanticSig)]
    -- ∀ α1:κ1 ... αN:κN . Σ → Ξ
  | FunctorSem !(Bind [(TyVar, Embed Kind)] SemanticFunctor)
    -- Dist Ξ
  | ModelSem AbstractSig
    deriving (Show, Typeable, Generic)

data SemanticFunctor =
  -- Σ1 → ... Σn → Ξ
  SemanticFunctor ![SemanticSig] !AbstractSig
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
  return $ TRecord [(FSig, s `TArr` s)]
embedSemanticSig (DataSem tabs tconc k) = do
  -- the embedding for a datatype witnesses the coercion from δ to {c1 : τ1 | ⋯ | cN : τN }
  a <- U.lfresh $ U.s2n "γ"
  let
    tConsume = TApp (TV a) tabs
    tProduce = TApp (TV a) tconc
    tEmbed = TForall $ U.bind (a, U.embed $ k `KArr` KType) $ TArr tConsume tProduce
  return $ TRecord [(FData, tEmbed)]
embedSemanticSig (ConSem t _) =
  return $ TRecord [(FCon, t)]
embedSemanticSig (ModSem fas) = do
  fts <- forM fas $ \(f, s) -> do
    t <- embedSemanticSig s
    return (f, t)
  return $ TRecord fts
embedSemanticSig (FunctorSem bnd) =
  embedSemanticFunctor bnd
embedSemanticSig (ModelSem abstr) = do
  t <- embedAbstractSig abstr
  return $ TDist t

embedSemanticFunctor :: LFresh m =>
                        U.Bind [(TyVar, U.Embed Kind)] SemanticFunctor
                        -> m Type
embedSemanticFunctor bnd =
  U.lunbind bnd $ \(tvks, SemanticFunctor doms cod) -> do
    domTs <- mapM embedSemanticSig doms
    codT <- embedAbstractSig cod
    return $ closeForalls tvks $ domTs `tArrs` codT

embedAbstractSig :: LFresh m => AbstractSig -> m Type
embedAbstractSig (AbstractSig bnd) =
  U.lunbind bnd $ \(tvks, sig) -> do
    t <- embedSemanticSig sig
    return $ tExists' tvks t

closeForalls :: [(TyVar, Embed Kind)] -> Type -> Type
closeForalls [] = id
closeForalls (ak:aks) =
  TForall . U.bind ak . closeForalls aks
