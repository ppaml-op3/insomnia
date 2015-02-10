-- | Signature subsumption relation: Γ ⊢ Ξ ≤ Ξ' ⇝ f
-- 
-- The relation produces a term Γ ⊢ f : ↓Ξ → ↓Ξ' (where ↓· is the
-- embedding of signatures into FOmega).
module FOmega.SubSig where

import Prelude hiding (mapM)
import Control.Monad (MonadPlus)

import Data.Traversable (Traversable(..))

import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh(..))
import qualified Unbound.Generics.LocallyNameless as U

import FOmega.Syntax
import FOmega.SemanticSig
import FOmega.MatchSigs (matchSubst)

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
   (FunctorSem _, FunctorSem _) -> fail "unimplemented"
   (_, _) -> fail "internal error: sigSubtyping of unequal signatures"

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
