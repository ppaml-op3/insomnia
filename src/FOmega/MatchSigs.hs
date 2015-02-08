-- | Semantic signature matching
--    Γ ⊢ Σ ≤ ∃αs.Σ' ↑ τs ⇝ f
--
-- The concrete signature on the left is said to match the abstract
-- signature on the right if we can find some types τs (such that Γ ⊢
-- τ : κₐ ) such that Γ ⊢ Σ ≤ Σ'[τs/αs] ⇝ f (where this latter
-- judgment is signature subtyping.  The difference is that matching
-- is concerned with finding the concrete types in the LHS that stand
-- for the abstract types in the RHS, while subtyping is about width
-- and depth subtyping of records).
--
-- The "F-ing modules" journal paper gives a decidable algorithm
-- "lookup_αs(Σ,Σ') ↑ τs" for signature matching in Section 5.2.  The
-- algorithm is complete provided that all the signatures in Γ are
-- valid and the signature ∃αs.Σ' is explicit (see paper for
-- definitions of explicitness and validity).  It is a theorem that
-- the lookup algorithm finds the τs that satisfy the matching
-- judgment.
--
-- The lookup algorithm for a single variable α is essentially: if Σ
-- is TypeSem τ and Σ' are both TypeSem and Σ' is in fact TypeSem (FV
-- α) then return τ.  Otherwise we only care about Σ' that is a record
-- (because functors (and models) close over their abstract variables
-- due to generativity): we pick out the set of fields common to Σ and Σ' and
-- nondeterministically guess which of them will succeed in looking up α.
--
-- In the implementation below, we look for all the variables at once,
-- and instead of non-deterministically guessing, we thread a "looking
-- for" set of variables in a state monad and write out τ,α pairs when
-- we find something appropriate.
module FOmega.MatchSigs where

import Control.Monad.State
import Control.Monad.Writer

import qualified Data.Set as S
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh (..))
import qualified Unbound.Generics.LocallyNameless as U

import FOmega.Syntax
import FOmega.SemanticSig

type MatchPairs = Endo [(TyVar, Type)]
type LookingSet = S.Set TyVar

type M m = WriterT MatchPairs (StateT LookingSet m)

-- | Consider the judgment Γ ⊢ Σ ≤ ∃αs.Σ' ↑ τs ⇝ f .  This function
-- 'matchSubst' takes Σ and ∃αs.Σ' and returns Σ'[τs/αs] and τs.  Where Γ⊢ τ:κₐ
matchSubst :: (MonadPlus m, LFresh m) => SemanticSig -> AbstractSig -> m (SemanticSig, [Type])
matchSubst lhs (AbstractSig bnd) =
  U.lunbind bnd $ \(tvks, rhs) -> do
    let alphas = map fst tvks
        lookingFor = S.fromList alphas
    (w, notFound) <- runStateT (execWriterT (lookupMatch lhs rhs)) lookingFor
    guard (S.null notFound)
    let subst = appEndo w []
        ans = (rhs, map TV alphas)
    return $ U.substs subst ans

lookupMatch :: Monad m => SemanticSig -> SemanticSig -> M m ()
lookupMatch (TypeSem tau _k1) (TypeSem (TV a) _k2) = do
  looking <- gets (S.member a)
  when looking $ do
    modify (S.delete a)
    tell $ Endo ((a,tau) :)
lookupMatch (ModSem fs1) (ModSem fs2) = do
  let commonFields = intersectFields fs1 fs2
  mapM_ (uncurry lookupMatch) commonFields
lookupMatch _ _ = return ()

intersectFields :: [(Field, a)] -> [(Field, b)] -> [(a,b)]
intersectFields fs1 fs2 = let
  m1 = M.fromList fs1
  m2 = M.fromList fs2
  i = M.intersectionWith (\x y -> (x, y)) m1 m2
  in M.elems i
