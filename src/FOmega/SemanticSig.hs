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
  -- [= δ = {f1:τ1 | … | fN:τN} : κ]
  | DataSem !TyVar !DataTypeSem !Kind
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

newtype DataTypeSem =
  -- λαs:κs. f1 (τ11,…,τn1), ⋯ , fN (τN1,…,τmN)
  -- we assume that the fields are all FUser and correspond to the constructors,
  -- and that they refer to a free variable δ (of kind κs → ⋆) which corresponds to the
  -- recursive occurrences of the datatype itself
  DataTypeSem (Bind [(TyVar, Embed Kind)] [(Field, [Type])])
  deriving (Show, Typeable, Generic)

instance Alpha SemanticSig
instance Alpha SemanticFunctor
instance Alpha AbstractSig
instance Alpha DataTypeSem

instance Subst Type SemanticSig
instance Subst Type SemanticFunctor
instance Subst Type AbstractSig
instance Subst Type DataTypeSem

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
embedSemanticSig (DataSem d dt k) = embedDataTypeSem d k dt
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

-- | embed a datatype into the type language
--   δ ≙ lfp λδ:κs→⋆. λαs:κs. f1(τ11,…,τn1), ⋯, fN(τ1N,…,τmN)
-- becomes
--   { dataOut : ∀γ:(κs→⋆)→⋆ . γ δ → γ (λαs:κs . {f1 : ⊗τ1s | ⋯ | fN : ⊗τNs })
--   , dataIn : { f1 : ∀αs:κs . τ1s → δ αs ; … ; fN : ∀αs:κs . τNs → δ αs }
--   }
-- where δ is assumed to be free (and will usually be existentially quantified somewhere in
-- the surrounding context.
--
-- That is, dataOut converts δ (in some sort of type context) to a sum
-- type of constructors, and dataIn is a record of injection
-- functions.
embedDataTypeSem :: LFresh m => TyVar -> Kind -> DataTypeSem -> m Type
embedDataTypeSem dataTyVar kData (DataTypeSem bnd) =
  U.lunbind bnd $ \(tvks_, conFArgs) -> do
    let tvks = map (\(f,ek) -> (f, U.unembed ek)) tvks_
    outTy <- dataTypeOut tvks conFArgs
    inTy <- dataTypeIn tvks conFArgs
    return $ TRecord [(FDataOut, outTy),
                      (FDataIn, inTy)]
  where
    dataTypeOut tvks conFArgs = do
      let conTys = flip map conFArgs $ \(fld, args) ->
            (fld, tupleT args)
          codLam = tLams tvks (TSum conTys)
      vg <- U.lfresh (U.s2n "γ")
      let g = TV vg
          kg = kData `KArr` KType
      return $ TForall $ U.bind (vg, U.embed kg) $ (g `TApp` TV dataTyVar) `TArr` (g `TApp` codLam)
    dataTypeIn tvks conFArgs = 
      let d = TV dataTyVar `tApps` (map (TV . fst) tvks)
          conTys = flip map conFArgs $ \(fld, args) ->
            (fld, tForalls tvks $ args `tArrs` d)
      in return $ TRecord conTys

closeForalls :: [(TyVar, Embed Kind)] -> Type -> Type
closeForalls [] = id
closeForalls (ak:aks) =
  TForall . U.bind ak . closeForalls aks
