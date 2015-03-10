-- | Signature subsumption relation: Γ ⊢ Ξ ≤ Ξ' ⇝ f
-- 
-- The relation produces a term Γ ⊢ f : ↓Ξ → ↓Ξ' (where ↓· is the
-- embedding of signatures into FOmega).
{-# LANGUAGE ScopedTypeVariables #-}
module FOmega.SubSig where

import Prelude hiding (mapM)
import Control.Monad (MonadPlus, zipWithM)

import Data.Traversable (Traversable(..))

import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh(..))
import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.FreshName

import FOmega.Syntax
import FOmega.SemanticSig
import FOmega.MatchSigs (matchSubst, matchSubsts)

type Coercion = Term

-- λ x : τ . x
idFun :: Type -> Term
idFun t =
  let x = U.s2n "x"
  in Lam $ U.bind (x, U.embed t) $ V x

fun :: LFresh m => Type -> (Term -> m Term) -> m Term
fun t f = do
  x <- U.lfresh $ U.s2n "x"
  e <- U.avoid [U.AnyName x] $ f (V x)
  return $ Lam $ U.bind (x, U.embed t) e

-- Λ α : κ → ⋆. λ x : α τ . x
reflFun :: LFresh m => Type -> Kind -> m Term
reflFun t k = do
  a <- U.lfresh $ U.s2n "α"
  let knd = k `KArr` KType
      typ = TV a `TApp` t
  return $ PLam $ U.bind (a, U.embed knd) $ idFun typ


valSemTerm :: Term -> Term
valSemTerm e = Record [(FVal, e)]

typeSemTerm :: LFresh m => Type -> Kind -> m Term
typeSemTerm t k = reflFun t k

sigSemTerm :: LFresh m => AbstractSig -> m Term
sigSemTerm a = do
  t <- embedAbstractSig a
  return $ idFun t

termSubtyping :: LFresh m => Type -> Type -> m Coercion
termSubtyping lhs rhs = do
  --  eq <- tyEquiv lhs rhs KType
  -- guard eq
  return $ idFun lhs

sigSubtyping :: (MonadPlus m, LFresh m) => SemanticSig -> SemanticSig -> m Coercion
sigSubtyping lhs rhs = do
  lhsTy <- embedSemanticSig lhs
  case (lhs, rhs) of
   (ValSem tl, ValSem tr) -> do
     f <- termSubtyping tl tr
     fun lhsTy $ \x -> return (f `App` (x `Proj` FVal))
   (TypeSem tl kl, TypeSem tr kr) -> do
     -- eq <- tyEquiv tl tr kl
     -- guard eq
     return $ idFun lhsTy
   (SigSem sl, SigSem sr) -> do
     _f1 <- abstractSigSubtyping sl sr
     _f2 <- abstractSigSubtyping sr sl
     fun lhsTy $ \_x -> sigSemTerm sr
   (ModSem modl, ModSem modr) -> do
     -- check that keys of modr are a subset of the keys of modl,
     -- so the intersection of the keys is in fact the rhs
     let ml = M.fromList modl
         mr = M.fromList modr
         m = M.intersectionWith (\x y -> (x, y)) ml mr
     m' <- mapM (uncurry sigSubtyping) m
     fun lhsTy $ \x -> do
       let rs = M.mapWithKey (\fld coer -> coer `App` (x `Proj` fld)) m'
       return $ Record $ M.toList rs
   (FunctorSem bndl, FunctorSem bndr) ->
     functorSubtyping bndl bndr
   (ModelSem absL, ModelSem absR) ->
     modelSubtyping absL absR
   (_, _) -> fail ("internal error: sigSubtyping of unequal signatures " ++ show lhs ++ " vs " ++ show rhs)

abstractSigSubtyping :: (MonadPlus m, LFresh m) => AbstractSig -> AbstractSig -> m Coercion
abstractSigSubtyping lhs@(AbstractSig bndl) rhs@(AbstractSig rhsBndl) = do
  lhsTy <- embedAbstractSig lhs
  U.lunbind bndl $ \(tvks, sigl) -> do
    -- extend environment
    (sigr, taus) <- matchSubst sigl rhs
    coer <- sigSubtyping sigl sigr
    fun lhsTy $ \x -> do
      y <- U.lfresh (U.s2n "y")
      U.lunbind rhsBndl $ \(rhsVs, rhsSig) -> do
        rhsTy <- embedSemanticSig rhsSig
        let ep = (rhsVs, rhsTy)
        U.avoid [U.AnyName y]
          $ unpacks (map fst tvks) y x
          $ packs taus (App coer $ V y) ep

-- |   ⊢ ∀αs . Σs → Ξ ≤ ∀αs'. Σs' → Ξ' ⇝ f'
--
--   αs' ⊢ Σs' ≤ ∃αs . Σs ↑ τs ⇝ χs
--
--   αs' ⊢ Ξ[τs/αs] ≤ Ξ' ⇝ χbody
--
-- where f' = λf:(∀αs.Σs→Ξ).
--             Λ αs . λ y1:Σ1' . … λ yN:Σn' .
--               χbody (f [τs] (χ1 y1) ⋯ (χN yN))
functorSubtyping :: forall m . (MonadPlus m, LFresh m)
                    => (U.Bind [(TyVar, U.Embed Kind)] SemanticFunctor)
                    -> (U.Bind [(TyVar, U.Embed Kind)] SemanticFunctor)
                    -> m Coercion
functorSubtyping bndl bndr =
  U.lunbind bndr $ \(tvksr, (SemanticFunctor rhsArgs rhsBodySig)) -> do
    -- (extend environment)

    lhsTy <- embedSemanticFunctor bndl
    rhsArgTys <- mapM embedSemanticSig rhsArgs

    -- (χ1, ..., χn), τs, χbody
    (coerArgs, taus, coerBody) <- U.lunbind bndl $ \(tvksl, (SemanticFunctor lhsArgs lhsBodySig)) -> do
      let alphas = map fst tvksl
      (lhsArgs', taus) <- matchSubsts rhsArgs (alphas, lhsArgs)
      coerArgs <- zipWithM sigSubtyping rhsArgs lhsArgs'
      
      let substitution = zip alphas taus
          rhsBodySig' = U.substs substitution rhsBodySig
      coerBody <- abstractSigSubtyping lhsBodySig rhsBodySig'
      return (coerArgs, taus, coerBody)

    return undefined
    let argNames = map (\n -> "yArg" ++ show n) [1 .. length rhsArgTys]

    withFreshName "f" $ \inFunc ->
      withFreshNames (argNames :: [String]) $ \argYs -> 
      let
        -- χ = χbody (f [τs] (χ1 y1) ... (χn yn))
        coercion =
          coerBody `App` (((V inFunc) `pApps` taus) `apps` (zipWith App coerArgs $ map V argYs))
        -- λ f : (∀αs.Σ → Ξ) . Λ α's . λ ys : Σ's . χ
        coercionFn =
          Lam $ U.bind (inFunc, U.embed lhsTy) $ pLams' tvksr $ lams (zip argYs rhsArgTys) coercion
       in return coercionFn
          
-- |  ⊢ model Ξ ≤ model Ξ' ⇝ f'
--
--    ⊢ Ξ ≤ Ξ' ⇝ f
--
-- where f' = λx:Dist Ξ. let x ~ x in return (f x)  :: Dist Ξ → Dist Ξ'
modelSubtyping :: (MonadPlus m, LFresh m) => AbstractSig -> AbstractSig -> m Coercion
modelSubtyping lhsAbs rhsAbs = do
  lhsTy <- embedAbstractSig lhsAbs
  pureCoer <- abstractSigSubtyping lhsAbs rhsAbs
  let x = U.s2n "x"
      body  = Return (pureCoer `App` V x)
      letSamp = LetSample $ U.bind (x, U.embed (V x)) body
      m = Lam $ U.bind (x, U.embed lhsTy) letSamp
  return m
