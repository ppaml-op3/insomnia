{-# LANGUAGE ViewPatterns, FlexibleContexts #-}
module Insomnia.ToF.Expr where

import Control.Lens hiding (indices)
import Control.Monad.Reader
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (Embed)
import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier
import Insomnia.Expr
import Insomnia.Types (Label(..), TypePath(..))
import Insomnia.TypeDefn
import Insomnia.Common.Telescope

import qualified FOmega.Syntax as F

import Insomnia.ToF.Env
import Insomnia.ToF.Type 
import {-# SOURCE #-} Insomnia.ToF.Pattern (patternTranslation)

expr :: ToF m => Expr -> m F.Term
expr e_ =
  case e_ of
   V x -> do
     mx <- view (valEnv . at x)
     case mx of
      Nothing -> throwError "unexpected failure: ToF.expr variable not in scope"
      Just (xv, prov) ->
        return $ case prov of
                  LocalTermVar -> F.V xv
                  StructureTermVar {} -> F.Proj (F.V xv) F.FVal
   L l -> return $ F.L l
   C vc -> do
     (inX, fcon) <- valueConstructor vc
     return (inX `F.Proj` F.FDataIn `F.Proj` fcon)
   Q (QVar p f) -> do
     let
       findIt ident = do
         ma <- view (modEnv . at ident)
         case ma of
          Just (sig, x) -> return (sig, F.V x)
          Nothing -> throwError "ToF.expr: type path has unbound module identifier at the root"
     (_sig, m) <- followUserPathAnything findIt (ProjP p f)
     -- assume _sig is a F.ValSem
     return $ F.Proj m F.FVal
   Lam bnd ->
     U.lunbind bnd $ \((x, U.unembed -> ann), e) -> do
       (t', _k) <- annot ann
       withLocalVar x $ \x' -> do
           m <- expr e
           return $ F.Lam $ U.bind (x', U.embed t') m
   Instantiate e co -> do
     m <- expr e
     instantiationCoercion co m
   App e1 e2 -> do
     m1 <- expr e1
     m2 <- expr e2
     return $ F.App m1 m2
   Record les -> do
     fms <- forM les $ \(Label l, e) -> do
       m <- expr e
       return (F.FUser l, m)
     return $ F.Record fms
   Ann e _t -> expr e
   Return e -> liftM F.Return $ expr e
   Case e cls ann -> caseExpr e cls ann
   Let bnd -> do
     U.lunbind bnd $ \(bndings, body) ->
       letBindings bndings $ expr body

withLocalVar :: ToF m
                => Var
                -> (F.Var -> m res)
                -> m res
withLocalVar x kont =
  withFreshName (U.name2String x) $ \x' ->
  local (valEnv %~ M.insert x (x', LocalTermVar)) (kont x')

withLocalVars :: ToF m
                 => [Var]
                 -> ([F.Var] -> m res)
                 -> m res
withLocalVars [] kont = kont []
withLocalVars (v:vs) kont =
  withLocalVar v $ \v' ->
  withLocalVars vs $ \vs' -> kont (v':vs')


letBindings :: ToF m
               => Bindings
               -> m F.Term
               -> m F.Term
letBindings (Bindings tele) kont =
  traverseTelescopeContT (\bnding rest -> letBinding bnding $ rest ()) tele $ \_ -> kont

letBinding :: ToF m
                => Binding
                -> m F.Term
                -> m F.Term
letBinding bnding kont =
  case bnding of
   ValB (x, _ann) (U.unembed -> e) ->
     letSimple F.Let x e kont
   SampleB (x, _ann) (U.unembed -> e) ->
     letSimple F.LetSample x e kont
   TabB x (U.unembed -> tabFun) ->
     letTabFun x tabFun $ \_v' f -> do
       m <- kont
       return (f m)

annot :: ToF m
         => Annot -> m (F.Type, F.Kind)
annot (Annot mt) =
  case mt of
   Nothing -> throwError "unexpected failure: ToF.annot expected an annotation"
   Just t -> type' t

letSimple :: ToF m
             => (U.Bind (F.Var, Embed F.Term) F.Term -> F.Term)
             -> Var
             -> Expr
             -> m F.Term
             -> m F.Term
letSimple mkLet x e kont = do
  m <- expr e
  x' <- U.lfresh (U.s2n $ U.name2String x)
  mbody <- U.avoid [U.AnyName x']
           $ local (valEnv %~ M.insert x (x', LocalTermVar))
           $ kont
  return $ mkLet $ U.bind (x', U.embed m) mbody

-- forall (i1 :: T1) ... (iN :: TN) in
--   f j1 ... jM ~ e
-- where f may occur in e
--
-- becomes
--    let rec f : D(T1×⋯×TM → T) = mem λ(j1, ..., jM) . 〚e〛
--        f ~ f
--    in return λj1.⋯λjM.f(j1,…,jM)
letTabFun :: ToF m
             => Var
             -> TabulatedFun
             -> (F.Var -> (F.Term -> F.Term) -> m ans)
             -> m ans
letTabFun v (TabulatedFun bnd) kont =
  U.lunbind bnd $ \(indices, tabSample) ->
    withLocalVars (map fst indices) $ \is -> do
      (tys, _ks) <- liftM unzip $ mapM (annot . U.unembed . snd) indices
      let its = zip (map fst indices) (zip is tys)
      withLocalVar v $ \ v' -> do
        recBindings <- tabulatedSampleRec v' its tabSample
        let body = F.lams (map snd its)
                   $ F.App (F.V v') (F.tuple $ map F.V is)
            sampl = F.LetSample $ U.bind (v', U.embed $ F.V v') (F.Return body)
        kont v' (F.LetSample . U.bind (v', U.embed $ F.LetRec $ U.bind recBindings sampl))

--
-- tabulatedSampleRec "f" (i1:t1) ... (iN:tN) (j1...jM . e)
-- returns
--      rec f : t1×⋯×tN→ Dist t'  = mem λj . let j1 = j.#0  ... jM = j.#M-1 in [e]
tabulatedSampleRec :: ToF m
                      => F.Var
                      -> [(Var, (F.Var, F.Type))]
                      -> TabSample
                      -> m F.RecBindings
tabulatedSampleRec _v _is (TabSample _ _ (Annot Nothing)) =
  throwError "internal error: tabulatedSampleRec called with unannotated tabulated function"
tabulatedSampleRec v is (TabSample js body (Annot (Just resultTy))) = do
  (resultTy', _k) <- type' resultTy
  withFreshName "j" $ \j -> do
    (projects, tys) <- makeTabIndices is j js
    body' <- expr body
    let tCross = F.tupleT tys
        memType = F.TDist (tCross `F.TArr` resultTy')
        bodyLets = F.lets projects body'
        bodyLams = F.Lam $ U.bind (j, U.embed tCross) bodyLets
        recMem = (v, U.embed memType, U.embed $ F.Memo $  bodyLams)
    return $ U.rec [recMem]

makeTabIndices :: ToF m
                  => [(Var, (F.Var, F.Type))]
                  -> F.Var
                  -> [TabSelector]
                  -> m ([(F.Var, F.Term)], [F.Type])
makeTabIndices is j sels =
  let subj = F.V j
      m = M.fromList is
      findIt (TabIndex s) idx = do
        case M.lookup s m of
         Just (v,ty) -> return ((v, F.Proj subj (F.FTuple idx)), ty)
         Nothing -> throwError ("internal error: makeTabIndices selector not among the index vars")
  in liftM unzip $ zipWithM findIt sels [0..]
   
-- | Given a value constructor, returns the pair (inout, f) where
-- 'inout' is a term of type '{dataIn : ... ; dataOut : ...}' that
-- injects or projects the constructor arguments into (out of) the
-- data type, and 'f' is the field name among the 'fi's that
-- corresponds to this particular value constructor.
valueConstructor :: ToF m
                    => ValueConstructor
                    -> m (F.Term, F.Field)
valueConstructor (VCLocal valCon) = do
  mv <- view (valConEnv . at valCon)
  (inoutX, fld) <- case mv of
    Just a -> return a
    Nothing -> throwError "internal error: ToF.valueConstructor VCLocal valCon not in environment"
  return (F.V inoutX, fld)
valueConstructor (VCGlobal (Right (InferredValConPath (TypePath modPath fty) f))) = do
  let
    findIt ident = do
      ma <- view (modEnv . at ident)
      case ma of
       Just (sig, x) -> return (sig, F.V x)
       Nothing -> throwError "ToF.valueConstructor: constructor path has unbound module identifier at the root"
  (_, tyM) <- followUserPathAnything findIt (ProjP modPath fty)
  return (tyM, F.FCon f)
valueConstructor (VCGlobal (Left _)) =
  throwError "internal error: ToF.valueConstructor VCGlobal without datatype annotation"

-- | Given an instantiation coerction ∀αs.ρ ≤ [αs↦τs]ρ construct a function
-- of type  (∀αs.ρ) → [αs↦τs]ρ. Namely λx:(∀αs.ρ). x [τs]
-- and apply it to the subject.
-- (In practice we go ahead and beta reduce)
instantiationCoercion :: ToF m => InstantiationCoercion -> F.Term -> m F.Term
instantiationCoercion (InstantiationSynthesisCoercion _scheme args _result) subject = do
-- notionally, so something like:
--  (scheme', _) <- type' scheme
--  x <- U.lfresh $ U.s2n "x"
--  let body = F.pApps (F.V x) args'
--      co = F.Lam $ U.bind (x, U.embed scheme') body
--  return $ F.App co subject
-- but we can go ahead and do the beta reduction in place.
  args' <- mapM (liftM fst . type') args
  return $ F.pApps subject args'
    
caseExpr :: ToF m
            => Expr
            -> [Clause]
            -> Annot
            -> m F.Term
caseExpr subj clauses ann = do
  resultTy <- case ann of
               (Annot (Just resultTy)) -> return resultTy
               _ -> throwError "ToF.caseExpr: internal error - expected an annotated case expression"
  (resultTy', _k) <- type' resultTy
  subj' <- expr subj
  withFreshName "subjP" $ \v -> do
    caseTreeBnd <- patternTranslation v clauses resultTy'
    let (v', caseTree) = UU.unsafeUnbind caseTreeBnd
      in return (F.Let $ U.bind (v', U.embed subj') caseTree)
