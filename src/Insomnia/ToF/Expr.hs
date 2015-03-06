{-# LANGUAGE ViewPatterns #-}
module Insomnia.ToF.Expr where

import Control.Lens
import Control.Monad.Reader
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (Embed)
import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Identifier
import Insomnia.Expr
import Insomnia.Types (Label(..))
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
      Nothing -> fail "unexpected failure: ToF.expr variable not in scope"
      Just (xv, prov) ->
        return $ case prov of
                  LocalTermVar -> F.V xv
                  StructureTermVar {} -> F.Proj (F.V xv) F.FVal
   L l -> return $ F.L l
   C vc -> valueConstructor vc
   Q (QVar p f) -> do
     let
       findIt ident = do
         ma <- view (modEnv . at ident)
         case ma of
          Just (sig, x) -> return (sig, F.V x)
          Nothing -> fail "ToF.expr: type path has unbound module identifier at the root"
     (_sig, m) <- followUserPathAnything findIt (ProjP p f)
     -- assume _sig is a F.ValSem
     return $ F.Proj m F.FVal
   Lam bnd ->
     U.lunbind bnd $ \((x, U.unembed -> ann), e) -> do
       (t', _k) <- annot ann
       withFreshName (U.name2String x) $ \x' ->
         local (valEnv %~ M.insert x (x', LocalTermVar)) $ do
           m <- expr e
           return $ F.Lam $ U.bind (x', U.embed t') m
   Instantiate e co -> do
     m <- expr e
     f <- instantiationCoercion co
     return $ F.App f m
   App e1 e2 -> do
     m1 <- expr e1
     m2 <- expr e2
     return $ F.App m1 m2
   Record les -> do
     fms <- forM les $ \(Label l, e) -> do
       m <- expr e
       return (F.FUser l, m)
     return $ F.Record fms
   Ann {} -> fail "unexpected failure: ToF.expr saw an Ann term"
   Return e -> liftM F.Return $ expr e
   Case e cls -> caseExpr e cls
   Let bnd -> do
     U.lunbind bnd $ \(bndings, body) ->
       letBindings bndings $ expr body

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
   ValB (x, U.unembed -> ann) (U.unembed -> e) ->
     letSimple F.Let x ann e kont
   SampleB (x, U.unembed -> ann) (U.unembed -> e) -> 
     letSimple F.LetSample x ann e kont
   TabB {} -> fail "unimplemented ToF.letBinding TabB"

annot :: ToF m
         => Annot -> m (F.Type, F.Kind)
annot (Annot mt) =
  case mt of
   Nothing -> fail "unexpected failure: ToF.annot expected an annotation"
   Just t -> type' t

letSimple :: ToF m
             => (U.Bind (F.Var, Embed F.Term) F.Term -> F.Term)
             -> Var
             -> Annot
             -> Expr
             -> m F.Term
             -> m F.Term
letSimple mkLet x ann e kont = do
  (ty, _k) <- annot ann
  m <- expr e
  x' <- U.lfresh (U.s2n $ U.name2String x)
  mbody <- U.avoid [U.AnyName x']
           $ local (valEnv %~ M.insert x (x', LocalTermVar))
           $ kont
  return $ mkLet $ U.bind (x', U.embed m) mbody


valueConstructor :: ToF m
                    => ValueConstructor
                    -> m F.Term
valueConstructor (VCLocal valCon) = do
  mv <- view (valConEnv . at valCon)
  xv <- case mv of
    Just xv -> return xv
    Nothing -> fail "internal error: ToF.valueConstructor VCLocal valCon not in environment"
  return (F.Proj (F.V xv) F.FCon)
valueConstructor (VCGlobal (ValConPath modPath f)) = do
  let
    findIt ident = do
      ma <- view (modEnv . at ident)
      case ma of
       Just (sig, x) -> return (sig, F.V x)
       Nothing -> fail "ToF.valueConstructor: constructor path has unbound module identifier at the root"
  (_sig, m) <- followUserPathAnything findIt (ProjP modPath f)
  return (F.Proj m F.FCon)

-- | Given an instantiation coerction ∀αs.ρ ≤ [αs↦τs]ρ construct a function
-- of type  (∀αs.ρ) → [αs↦τs]ρ. Namely λx:(∀αs.ρ). x [τs]
instantiationCoercion :: ToF m => InstantiationCoercion -> m F.Term
instantiationCoercion (InstantiationSynthesisCoercion scheme args _result) = do
  (scheme', _) <- type' scheme
  args' <- mapM (liftM fst . type') args
  x <- U.lfresh $ U.s2n "x"
  let
    body = F.pApps (F.V x) args'
  return $ F.Lam $ U.bind (x, U.embed scheme') body
    
caseExpr :: ToF m
            => Expr
            -> [Clause]
            -> m F.Term
caseExpr subj clauses = do
  subj' <- expr subj
  withFreshName "subjP" $ \v -> do
    let resultTy = error "finish me: ToF.Expr.caseExpr needs a resultTy"
    caseTreeBnd <- patternTranslation v clauses resultTy
    let (v', caseTree) = UU.unsafeUnbind caseTreeBnd
      in return (F.Let $ U.bind (v', U.embed subj') caseTree)
