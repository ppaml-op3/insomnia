{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
-- | Type checking (and inference) for core language expressions.
module Insomnia.Typecheck.Expr where

import Control.Lens
import Control.Applicative ((<$>))
import Control.Monad (forM, when, unless, void, zipWithM)

import Data.List (foldl')
import Data.Monoid (Monoid(..), (<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.Literal
import Insomnia.Types (Kind(..), Type(..), Row(..), canonicalOrderRowLabels, freshUVarT)
import Insomnia.Expr

import Insomnia.Unify (applyCurrentSubstitution,
                       MonadUnify(..),
                       Unifiable(..),
                       )

import Insomnia.Pretty (Pretty)

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.Type (checkType)


checkLiteral :: Literal -> Type -> TC ()
checkLiteral (IntL {}) t = t =?= intT
checkLiteral (RealL {}) t = t =?= realT

checkVariable :: Pretty var
                 => (var -> TC (Maybe Type))
                 -> (var -> Expr)
                 -> var
                 -> Type
                 -> TC Expr
checkVariable lookupV mkV v t_ = do
  mt <- lookupV v
  case mt of
    Nothing -> typeError ("unbound variable " <> formatErr v)
    Just tv -> instantiate tv $ \t' -> do
      t_ =?= t'
      return $ mkV v

checkExpr :: Expr -> Type -> TC Expr
checkExpr e_ t_ = case e_ of
  Lam bnd ->
    U.lunbind bnd $ \ ((v, U.unembed -> ann), e) -> do
      (tdom, tcod) <- unifyFunctionT t_
      unifyAnn tdom ann
      e' <- extendLocalCtx v tdom $ checkExpr e tcod
      tannot <- applyCurrentSubstitution tdom
      return $ Lam (U.bind (v, U.embed $ Annot $ Just tannot) e')
  L l -> do
    checkLiteral l t_
    return (L l)
  V v -> checkVariable lookupLocal V v t_
  Q q -> checkVariable (fmap (fmap fst) . lookupGlobal) Q q t_
  C c -> do
    constr <- lookupValueConstructor c
    ty <- mkConstructorType constr
    instantiate ty $ \ty' -> do
      ty' =?= t_
      return $ C c
  App e1_ e2_ -> do
    (t1, e1') <- inferExpr e1_
    (tdom, tcod) <- unifyFunctionT t1
                    <??@ ("while trying to apply " <> formatErr e1_
                          <> " to " <> formatErr e2_)
    e2' <- checkExpr e2_ tdom
           <??@ ("when checking argument " <> formatErr e2_
                 <> " of " <> formatErr e1_)
    tcod =?= t_ <??@ ("expecting " <> formatErr t_
                      <> " but got result " <> formatErr tcod
                      <> " when applying " <> formatErr e1_
                      <> " to " <> formatErr e2_)
    return $ App e1' e2'
  Record les -> do
    (les', lts) <- fmap unzip $ forM les $ \(lbl,e) -> do
      tu <- freshUVarT
      e' <- checkExpr e tu
      return ((lbl, e'), (lbl, tu))
    let row = Row $ canonicalOrderRowLabels lts
    (TRecord row) =?= t_
    return (Record les')
  Let bnd ->
    U.lunbind bnd $ \(binds, body) ->
    checkBindings binds $ \ binds' -> do
      -- if any of the bindings perform a sampling operation,
      -- the body had better be a distribution of some sort
      when (anyBindings isStochasticBinding binds') $ do
        void $ unifyDistT t_
      body' <- checkExpr body t_
      return $ Let $ U.bind binds' body'
  Case scrut clauses -> do
    (tscrut, scrut') <- inferExpr scrut
    clauses' <- forM clauses (checkClause tscrut t_)
                <??@ ("while checking case expression " <> formatErr e_)
    return $ Case scrut' clauses'
  Ann e1_ t1_ -> do
    t1 <- checkType t1_ KType
    e1 <- checkExpr e1_ t1
          <??@ ("while checking " <> formatErr e1_
                <> "against type annotation " <> formatErr t_)
    t1 =?= t_
    return (Ann e1 t1)
  Return e1_ -> do
    t1 <- unifyDistT t_
    e1 <- checkExpr e1_ t1
    return (Return e1)

type PatternMatch = [(Var, Type)]

-- | check that the give clause scrutenized the given type and returns
-- a result of the expected result type.
checkClause :: Type -> Type -> Clause -> TC Clause
checkClause tscrut texp cls@(Clause bnd) =
  U.lunbind bnd $ \ (pat, expr) -> do
    (pat', match) <- (checkPattern tscrut pat)
                     <??@ ("while checking clause " <> formatErr cls)
    expr' <- (extendLocalsCtx match $ checkExpr expr texp)
             <??@ ("while checking expression of clause " <> formatErr cls)
    return $ Clause $ U.bind pat' expr'

checkPattern :: Type -> Pattern -> TC (Pattern, PatternMatch)
checkPattern tscrut p =
  case p of
    WildcardP -> return (p, [])
    VarP v -> return (p, [(v, tscrut)])
    RecordP lps -> do
      (mss, lps', lts) <- fmap unzip3 $ forM lps $ \(U.unembed -> lbl, pat) -> do
        tp <- freshUVarT
        (pat', ms) <- checkPattern tp pat
        return (ms, (U.embed lbl, pat'), (lbl, tp))
      let ms = mconcat mss
          row = Row $ canonicalOrderRowLabels lts
      tscrut =?= TRecord row
      return (RecordP lps', ms)
    ConP (U.unembed -> c) ps -> do
      alg <- lookupValueConstructor c
      instantiateConstructorArgs (alg^.algConstructorArgs) $ \ tparams targs -> do
        unless (length ps == length targs) $
          typeError ("constructor " <> formatErr c
                     <> " should take " <> formatErr (length targs)
                     <> " arguments, but pattern matches "
                     <> formatErr (length ps)
                     <> " arguments")
        let d = alg^.algConstructorDCon
            -- data type of the constructor applied to the
            -- fresh unification vars
            dty = foldl' TApp (TC d) tparams
        tscrut =?= dty
        (ps', ms) <- unzip <$> zipWithM checkPattern targs ps
        return (ConP (U.embed c) ps', mconcat ms)
-- | check a sequence of bindings and pass them to the given continuation
-- in an environment suitably extended by the new bindings.
checkBindings :: Bindings -> (Bindings -> TC a) -> TC a
checkBindings NilBs kont = kont NilBs
checkBindings (ConsBs (U.unrebind -> (bind, binds))) kont =
  checkBinding bind $ \bind' ->
  checkBindings binds $ \ binds' ->
  kont (ConsBs (U.rebind bind' binds'))

checkBinding :: Binding -> (Binding -> TC a) -> TC a
checkBinding (ValB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (t, e') <- inferExpr e
      -- XXX : TODO generalize uvars, or else freeze 'em if we're going to
      -- behave like recent versions of GHC
      extendLocalCtx v t $ do
        tannot <- applyCurrentSubstitution t
        kont $ ValB (v, U.embed $ Annot $ Just tannot) (U.embed e')
    Annot (Just t) -> do
      void $ checkType t KType
      e' <- checkExpr e t
      extendLocalCtx v t $ do
        tannot <- applyCurrentSubstitution t
        kont $ ValB (v, U.embed $ Annot $ Just tannot) (U.embed e')
checkBinding (SampleB (v, U.unembed -> ann) (U.unembed -> e)) kont =
  case ann of
    Annot Nothing -> do
      (tdist, e') <- inferExpr e
      tsample <- unifyDistT tdist
      extendLocalCtx v tsample $ do
        tannot <- applyCurrentSubstitution tsample
        kont $ SampleB (v, U.embed $ Annot $ Just tannot) (U.embed e')
    Annot (Just tsample) -> do
      void $ checkType tsample KType
      e' <- checkExpr e (distT tsample)
      extendLocalCtx v tsample $ do
        tannot <- applyCurrentSubstitution tsample
        kont $ SampleB (v, U.embed $ Annot $ Just tannot) (U.embed e')
checkBinding (TabB y (U.unembed -> tf)) kont =
  checkTabulatedFunction y tf kont

checkTabulatedFunction :: Var -> TabulatedFun -> (Binding -> TC a) -> TC a
checkTabulatedFunction y (TabulatedFun bnd) kont =
  U.lunbind bnd $ \(avs, TabSample sels e) -> do
    -- map each var to a uvar unified with the var's typing annotation
    vts <- forM avs $ \(v, U.unembed -> a) -> do
      tu <- freshUVarT
      unifyAnn tu a
      return (v, tu)
    (sels', selTys, e', tdist) <-
      extendLocalsCtx vts $ settingVisibleSelectors (map fst vts) $ do
        (sels', selTys) <- unzip <$> mapM inferTabSelector sels
        (tdist, e') <- inferExpr e
        return (sels', selTys, e', tdist)
    tsample <- unifyDistT tdist
    let tfun = functionT' selTys tsample
    extendLocalCtx y tfun
      $ kont $ TabB y (U.embed $ TabulatedFun $ U.bind avs $ TabSample sels' e')

inferTabSelector :: TabSelector -> TC (TabSelector, Type)
inferTabSelector (TabIndex v) = do
  ensureVisibleSelector v
  mty <- lookupLocal v
  ty <- case mty of
    Nothing -> typeError ("selector " <> formatErr v <> " is not in scope??")
    Just ty -> return ty
  return (TabIndex v, ty)

inferLiteral :: Literal -> TC Type
inferLiteral (IntL {}) = return intT
inferLiteral (RealL {}) = return realT

inferExpr :: Expr -> TC (Type, Expr)
inferExpr e_ = case e_ of
  V v -> do
    mt <- lookupVar v
    case mt of
      Nothing -> typeError ("unbound variable " <> formatErr v)
      Just tv -> instantiate tv $ \t' -> 
        return (t', V v)
  Q qvar -> do
    mt <- lookupGlobal qvar
    case mt of
      Nothing -> typeError ("unbound variable " <> formatErr qvar)
      Just (tv, _stoch) -> instantiate tv $ \t' ->
        return (t', Q qvar)
  App e1_ e2_ -> do
    (t1, e1') <- inferExpr e1_
    (tdom, tcod) <- unifyFunctionT t1
                    <??@ ("while trying to apply " <> formatErr e1_ <> " to " <> formatErr e2_)
    e2' <- checkExpr e2_ tdom
           <??@ ("when checking argument " <> formatErr e2_
                 <> " of " <> formatErr e1_)
    return (tcod, App e1' e2')
  L lit -> do
    t <- inferLiteral lit
    return (t, e_)
  C c -> do
    constr <- lookupValueConstructor c
    ty <- mkConstructorType constr
    return (ty, C c)
  Ann e1_ t_ -> do
    t <- checkType t_ KType
         <??@ ("while checking type annotation " <> formatErr e_)
    e1' <- checkExpr e1_ t
           <??@ ("while checking " <> formatErr e1_
                 <> "against type annotation " <> formatErr t_)
    tannot <- applyCurrentSubstitution t
    return (t, Ann e1' tannot)
  Record les -> do
    ltes <- forM les $ \(lbl, e) -> do
      (t, e') <- inferExpr e
      return (lbl, t, e')
    let les' = map (\(lbl, _t, e) -> (lbl, e)) ltes
        lts_ = map (\(lbl, t, _e) -> (lbl, t)) ltes
        row = Row $ canonicalOrderRowLabels lts_
    return (TRecord row, Record les')
  Case {} -> typeError ("cannot infer the type of a case expression "
                        <> formatErr e_
                        <> " try adding a type annotation"
                        <> " or a function signature declaration")
  Lam bnd ->
    U.lunbind bnd $ \((v, U.unembed -> ann), e1_) -> do
      tdom <- freshUVarT
      tcod <- freshUVarT
      unifyAnn tdom ann
      e1 <- extendLocalCtx v tdom $ checkExpr e1_ tcod
      tanndom <- applyCurrentSubstitution tdom
      tanncod <- applyCurrentSubstitution tcod
      let
        e = Lam $ U.bind (v, U.embed $ Annot $ Just tanndom) (Ann e1 tanncod)
        t = functionT tdom tcod
      return (t, e)
  Return e1 -> do
    (t1, e1') <- inferExpr e1
    return (distT t1, Return e1')
  _ -> typeError ("cannot infer type of " <> formatErr e_
                  <> " try adding a type annotation")

ensureVisibleSelector :: Var -> TC ()
ensureVisibleSelector v = do
  m <- view (envVisibleSelector . at v)
  case m of
    Just () -> return ()
    Nothing -> typeError (formatErr v
                          <> " is not a selector from "
                          <> "the immediately enclosing 'forall'")

-- | Given a type ∀ α1∷K1 ⋯ αN∷KN . τ, pick fresh unification vars u1,…,uN
-- and pass τ[u/α] to the given continuation.
instantiate :: Type -> (Type -> TC a) -> TC a
instantiate ty kont =
  case ty of
    TForall bnd -> U.lunbind bnd $ \ ((tv, _), ty') -> do
      tu <- TUVar<$> unconstrained
      instantiate (U.subst tv tu ty') kont
    _ -> kont ty

-- | Given α1∷ ⋯ αN.KN . 〈τ1, …, τM〉, pick fresh unification vars u1,…,uN
-- and pass 〈u1,…,uN〉 and 〈τ1[u/α], …, τM[u/α]〉 to the continuation
instantiateConstructorArgs :: ConstructorArgs -> ([Type] -> [Type] -> TC a) -> TC a
instantiateConstructorArgs bnd kont =
  U.lunbind bnd $ \ (tvks, targs) -> do
    tus <- mapM (\_-> freshUVarT) tvks
    -- the substitution taking each variable to a fresh unification var
    let
      s = zip (map fst tvks) tus
      targs' = U.substs s targs
    kont tus targs'

unifyAnn :: Type -> Annot -> TC ()
unifyAnn t1 (Annot (Just t2)) = do
  t2' <- checkType t2 KType
  t1 =?= t2'
unifyAnn _ _ = return ()

unifyFunctionT :: Type -> TC (Type, Type)
unifyFunctionT t = do
  tdom <- freshUVarT
  tcod <- freshUVarT
  t =?= functionT tdom tcod
  return (tdom, tcod)

unifyDistT :: Type -> TC Type
unifyDistT t = do
  tsample <- freshUVarT
  t =?= distT tsample
  return tsample

