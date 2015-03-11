-- | Signature subsumption relation: Γ ⊢ Ξ ≤ Ξ' ⇝ f
-- 
-- The relation produces a term Γ ⊢ f : ↓Ξ → ↓Ξ' (where ↓· is the
-- embedding of signatures into FOmega).
{-# LANGUAGE ScopedTypeVariables #-}
module FOmega.SubSig where

import Prelude hiding (mapM)
import Control.Lens
import Control.Monad (MonadPlus, zipWithM)

import Data.Traversable (Traversable(..))

import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh(..))
import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.FreshName

import FOmega.Syntax
import FOmega.SemanticSig
import FOmega.MatchSigs (matchSubst, matchSubsts)

-- | A coercion is a closed term of function type.
-- As it turns out, many coercions are just the identity function, so
-- do a bit of simplifications as we go.
-- (We could do even better if we represented composite coercions as values of this datatype.
--  For example if we saw  (DistCoer (IdCoer ty)) we could replace it by IdCoer (TDist ty)
--  instead of the more cumbersome  "λ x : Dist ty . let s ~ coerce@(id ty) x in return s"
--  But we get a lot of mileage just out of the id/non-id distinction and substitution of
--  coercion arguments for coercion results.)
data Coercion =
  IdCoer Type
  | LamCoer (U.Bind (Var, U.Embed Type) Term)

coercionTerm :: Coercion -> Term
coercionTerm (IdCoer ty) = idCoerTerm ty
coercionTerm (LamCoer bnd) = Lam bnd

-- λ x : τ . x
idCoerTerm :: Type -> Term
idCoerTerm t =
  let x = U.s2n "x"
  in Lam $ U.bind (x, U.embed t) $ V x

applyCoercion :: Coercion -> Term -> Term
applyCoercion (IdCoer _ty) m = m
applyCoercion (LamCoer bnd) m =
  U.runLFreshM $ 
  U.avoid (toListOf U.fvAny m) $ 
  U.lunbind bnd $ \ ((v, _ty), body) ->
  return (U.subst v m body)

-- given f : τ → σ , g : ρ → τ construct λ x : ρ . f (g x)) : ρ → σ
composeCoer :: Coercion -> Coercion -> Type -> Coercion
composeCoer f g t =
  let x = U.s2n "x"
  in LamCoer $ U.bind (x, U.embed t) $ f `applyCoercion` (g `applyCoercion` (V x))

coercion :: LFresh m => Type -> (Term -> m Term) -> m Coercion
coercion t f = do
  x <- U.lfresh $ U.s2n "x"
  e <- U.avoid [U.AnyName x] $ f (V x)
  return $ LamCoer $ U.bind (x, U.embed t) e

-- Λ α : κ → ⋆. λ x : α τ . x
reflFun :: LFresh m => Type -> Kind -> m Term
reflFun t k = do
  a <- U.lfresh $ U.s2n "α"
  let knd = k `KArr` KType
      typ = TV a `TApp` t
  return $ PLam $ U.bind (a, U.embed knd) $ coercionTerm $ IdCoer typ


valSemTerm :: Term -> Term
valSemTerm e = Record [(FVal, e)]

typeSemTerm :: LFresh m => Type -> Kind -> m Term
typeSemTerm t k = do
  m <- reflFun t k
  return $ Record [(FType, m)]

sigSemTerm :: LFresh m => AbstractSig -> m Term
sigSemTerm a = do
  t <- embedAbstractSig a
  return $ Record [(FSig, coercionTerm $ IdCoer t)]

termSubtyping :: LFresh m => Type -> Type -> m Coercion
termSubtyping lhs rhs = do
  --  eq <- tyEquiv lhs rhs KType
  -- guard eq
  return $ IdCoer lhs

sigSubtyping :: (MonadPlus m, LFresh m) => SemanticSig -> SemanticSig -> m Coercion
sigSubtyping lhs rhs = do
  lhsTy <- embedSemanticSig lhs
  case (lhs, rhs) of
   (ValSem tl, ValSem tr) -> do
     f <- termSubtyping tl tr
     coercion lhsTy $ \x -> return $ valSemTerm (applyCoercion f (x `Proj` FVal))
   (TypeSem tl kl, TypeSem tr kr) -> do
     -- eq <- tyEquiv tl tr kl
     -- guard eq
     return $ IdCoer lhsTy
   (SigSem sl, SigSem sr) -> do
     _f1 <- abstractSigSubtyping sl sr
     _f2 <- abstractSigSubtyping sr sl
     coercion lhsTy $ \_x -> sigSemTerm sr
   (ConSem {}, ConSem {}) -> return (IdCoer lhsTy)
   (DataSem {}, DataSem {}) -> return (IdCoer lhsTy)
   (DataSem {} , TypeSem tr kr) ->
     coercion lhsTy $ \_dk -> typeSemTerm tr kr
   (ModSem modl, ModSem modr) -> do
     -- check that keys of modr are a subset of the keys of modl,
     -- so the intersection of the keys is in fact the rhs
     let ml = M.fromList modl
         mr = M.fromList modr
         m = M.intersectionWith (\x y -> (x, y)) ml mr
     m' <- mapM (uncurry sigSubtyping) m
     coercion lhsTy $ \x -> do
       let rs = M.mapWithKey (\fld coer -> applyCoercion coer (x `Proj` fld)) m'
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
    coercion lhsTy $ \x -> do
      y <- U.lfresh (U.s2n "y")
      U.lunbind rhsBndl $ \(rhsVs, rhsSig) -> do
        rhsTy <- embedSemanticSig rhsSig
        let ep = (rhsVs, rhsTy)
        U.avoid [U.AnyName y]
          $ unpacks (map fst tvks) y x
          $ packs taus (applyCoercion coer $ V y) ep

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

    let argNames = map (\n -> "yArg" ++ show n) [1 .. length rhsArgTys]

    coercion lhsTy $ \inFunc ->
      withFreshNames (argNames :: [String]) $ \argYs -> 
      let
        -- χ = χbody (f [τs] (χ1 y1) ... (χn yn))
        coercion =
          applyCoercion coerBody ((inFunc `pApps` taus) `apps` (zipWith applyCoercion coerArgs $ map V argYs))
        -- Λ α's . λ ys : Σ's . χ
        resultFn = pLams' tvksr $ lams (zip argYs rhsArgTys) coercion
       in return resultFn
          
-- |  ⊢ model Ξ ≤ model Ξ' ⇝ f'
--
--    ⊢ Ξ ≤ Ξ' ⇝ f
--
-- where f' = λx:Dist Ξ. let x ~ x in return (f x)  :: Dist Ξ → Dist Ξ'
modelSubtyping :: (MonadPlus m, LFresh m) => AbstractSig -> AbstractSig -> m Coercion
modelSubtyping lhsAbs rhsAbs = do
  lhsTy_ <- embedAbstractSig lhsAbs
  let lhsTy = TDist lhsTy_
  pureCoer <- abstractSigSubtyping lhsAbs rhsAbs
  coercion lhsTy $ \d ->
    withFreshName "s" $ \s ->
    let body  = Return (applyCoercion pureCoer $ V s)
        letSamp = LetSample $ U.bind (s, U.embed d) body
    in return letSamp
