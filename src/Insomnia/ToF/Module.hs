{-# LANGUAGE ViewPatterns,
      FlexibleContexts, FlexibleInstances, TypeSynonymInstances
  #-}
module Insomnia.ToF.Module where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Data.Monoid (Monoid(..), (<>), Endo(..))
import qualified Data.Map as M

import qualified Unbound.Generics.LocallyNameless as U

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F
import qualified FOmega.MatchSigs as F
import qualified FOmega.SubSig as F

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModuleType
import Insomnia.Module
import Insomnia.Expr

import Insomnia.ToF.Env
import Insomnia.ToF.Summary
import Insomnia.ToF.Type
import Insomnia.ToF.Expr
import Insomnia.ToF.ModuleType


---------------------------------------- Modules

moduleExpr :: ToF m => ModuleExpr -> m (F.AbstractSig, F.Term)
moduleExpr mdl_ =
  case mdl_ of
   ModuleStruct mdl -> structure ModuleMK mdl
   ModuleSeal me mt -> sealing me mt
   ModuleAssume mty -> moduleAssume mty
   ModuleId p -> do
     (sig, m) <- modulePath p
     return (F.AbstractSig $ U.bind [] sig, m)
   ModuleFun bnd ->
     U.lunbind bnd $ \(tele, bodyMe) ->
     moduleFunctor tele bodyMe
   ModuleApp pfun pargs -> moduleApp pfun pargs
   ModuleModel mdl -> modelExpr mdl

modelExpr :: ToF m => ModelExpr -> m (F.AbstractSig, F.Term)
modelExpr mdle =
  case mdle of
   ModelStruct str -> do
     (sigStr, m) <- structure ModelMK str
     let
       sig = F.ModelSem sigStr
       s = F.AbstractSig $ U.bind [] sig
     return (s, m)
   ModelId p -> do
     (sig, m) <- modulePath p
     return (F.AbstractSig $ U.bind [] sig, m)
   ModelLocal lcl bdy mt ->
     modelLocal lcl bdy mt

moduleAssume :: ToF m
                => ModuleType
                -> m (F.AbstractSig, F.Term)
moduleAssume modTy = do
  absSig <- moduleType modTy
  ty <- F.embedAbstractSig absSig
  return (absSig, F.Assume ty)

structure :: ToF m => ModuleKind -> Module -> m (F.AbstractSig, F.Term)
structure mk (Module decls) = do
  declarations mk decls $ \(summary@(tvks,sig), fields, termHole) -> do
    let semSig = F.ModSem sig
    ty <- F.embedSemanticSig semSig
    let r = F.Record fields
        m = retMK mk $ F.packs (map (F.TV . fst) tvks) r (tvks, ty)
    return (mkAbstractModuleSig summary, appEndo termHole m)
  where
    retMK :: ModuleKind -> F.Term -> F.Term
    retMK ModuleMK = id
    retMK ModelMK = F.Return
    
-- | 〚let { decls } in M : S〛 Unlike the F-ing modules calculus
-- where "let B in M" is explained as "{ B ; X = M}.X", because we're
-- in a monadic language in the model fragment, this is a primitive
-- construct.  Suppose 〚 {decls} 〛 = e₁ : Dist ∃αs.Σ₁  and 〚S〛= ∃βs.Σ₂
-- and 〚Γ,αs,X:Σ₁⊢ M[X.ℓs/ℓs]〛= e₂ : Dist ∃γs.Σ₃ then
-- the local module translates as:
--
--   let Y ~ e₁ in unpack αs,X = Y in
--   let Z ~ e₂ in unpack γs,W = Z in
--   return (pack τs (f W) as ∃βs.Σ₂)
--
-- where αs,γs⊢ Σ₃ ≤ ∃βs.Σ₂ ↑ τs ⇝ f is the signature sealing coercion;
-- all the locals are fresh; and the [X.ℓs/ℓs] means to put in
-- projections from X for all the declarations in decls that appear in
-- e₂
--
-- The big picture is: we have two "monads", the distribution monad
-- and the existential packing "monad", so we use the elim forms to
-- take them both apart, and then return/pack the resulting modules.
modelLocal :: ToF m => Module -> ModelExpr -> ModuleType -> m (F.AbstractSig, F.Term)
modelLocal lcl_ body_ mt_ = do
  ascribedSig <- moduleType mt_
  let (Module lclDecls) = lcl_
  declarations ModelMK lclDecls $ \(_lclSummary, _lclFields, lclTermHole) -> do
    (F.AbstractSig bodySigBnd, bodyTerm) <- modelExpr body_
    U.lunbind bodySigBnd $ \(gammas,bodySig) -> do
      (taus, coer) <- do
        (sig2, taus) <- F.matchSubst bodySig ascribedSig
        coercion <- F.sigSubtyping bodySig sig2
        return (taus, coercion)
      z <- U.lfresh (U.string2Name "z")
      w <- U.lfresh (U.string2Name "w")
      packsAnnotation <- do
        let (F.AbstractSig bnd) = ascribedSig
        U.lunbind bnd $ \ (betas, s) -> do
          ty <- F.embedSemanticSig s
          return (betas, ty)
      let
        finalOut = F.packs taus (F.applyCoercion coer (F.V w)) packsAnnotation
      unpackedGammas <- F.unpacks (map fst gammas) w (F.V z) $ finalOut
      let
        withE2 = F.Let $ U.bind (z, U.embed bodyTerm) unpackedGammas
        localTerm = appEndo lclTermHole withE2
        localSig = F.AbstractSig $ U.bind [] $ F.ModelSem ascribedSig
      return (localSig, localTerm)

-- | In the F-ing modules paper, (M:>S) is syntactic sugar, and only
-- (X :> S) is primitive.  But if we expand out the sugar and apply
-- some commuting conversions, we get something in nice form and we
-- choose to implement that nice form.
--
--    
--  〚(M :> S)〛 = 〚({ X = M ; X' = (X :> S) }.X')〛
--    = unpack (αs, y) = 〚{ X = M ; X' = (X :> S)}〛in pack (αs, y.lX')
--    = unpack (αs, y) = (unpack (βs, z1) = 〚M〛in unpack (γs, z2) = 〚(X :> S)〛[z1 / X] in pack (βs++γs, { lX = z1 ; lX' = z2 })) in pack (αs, y.lX')
--    = unpack (βs, z1) = 〚M〛in unpack (γs, z2) = 〚(X :> S)〛[z1/X] in unpack (αs,y) = pack (βs++γs, { lX = X ; lX' = z2 }) in pack (αs, y.lX')
--    = unpack (βs, z1) = 〚M〛 in unpack (γs, z2) = 〚(X :> S)〛[z1/X] in pack (βs++γs, z2)
--    = unpack (βs, z1) = 〚M〛 in unpack (γs, z2) = pack (τs, f z1) in pack (βs++γs, z2) where Σ₁ ≤ Ξ ↑ τs ⇝ f where Σ₁ is the type of z1 and Ξ is 〚S〛
--    = unpack (βs, z1) = 〚M〛 in pack (βs++τs, f z1)
--
-- In other words, elaborate M and S and construct the coercion f and
-- discover the sealed types τs, then pack anything that M abstracted
-- together with anything that S seals.  (The one missing bit is the
-- type annotation on the "pack" term, but it's easy.  Suppose Ξ is
-- ∃δs.Σ₂, then the result has type ∃βs,δs.Σ₂)
sealing :: ToF m => ModuleExpr -> ModuleType -> m (F.AbstractSig, F.Term)
sealing me mt = do
  xi@(F.AbstractSig xiBnd) <- moduleType mt
  (F.AbstractSig sigBnd, m) <- moduleExpr me
  U.lunbind sigBnd $ \(betas, sigma) -> do
    (taus, coer) <- do
      (sig2, taus) <- F.matchSubst sigma xi
      coercion <- F.sigSubtyping sigma sig2
      return (taus, coercion)
    z1 <- U.lfresh (U.s2n "z")
    let
      packedTys = (map (F.TV . fst) betas)
                  ++ taus
    (xi', bdy) <- U.lunbind xiBnd $ \(deltas,sigma2) -> do
      sigma2emb <- F.embedSemanticSig sigma2
      let bdy = F.packs packedTys (F.applyCoercion coer $ F.V z1) (betas++deltas, sigma2emb)
          xi' = F.AbstractSig $ U.bind (betas++deltas) sigma2
      return (xi', bdy)
    term <- F.unpacks (map fst betas) z1 m bdy
    return (xi', term)

-- | (X1 : S1, ... Xn : Sn) -> { ... Xs ... }
-- translates to    Λα1s,...αns.λX1:Σ1,...,Xn:Σn. mbody : ∀αs.Σ1→⋯Σn→Ξ
-- where 〚Si〛= ∃αi.Σi and 〚{... Xs ... }〛= mbody : Ξ
moduleFunctor :: ToF m
                 => (Telescope (FunctorArgument ModuleType))
                 -> ModuleExpr
                 -> m (F.AbstractSig, F.Term)
moduleFunctor teleArgs bodyMe =
  withFunctorArguments teleArgs $ \(tvks, argSigs) -> do
    (resultAbs, mbody) <- moduleExpr bodyMe
    let funSig = F.SemanticFunctor (map snd argSigs) resultAbs
        s = F.FunctorSem $ U.bind tvks funSig
    args <- forM argSigs $ \(v,argSig) -> do
      argTy <- F.embedSemanticSig argSig
      return (v, argTy)
    let fnc = F.pLams' tvks $ F.lams args mbody
    return (F.AbstractSig $ U.bind [] s,
            fnc)

-- | p (p1, .... pn) becomes  m [τ1s,…,τNs] (f1 m1) ⋯ (fn mn) : Ξ[τs/αs]
-- where 〚p〛 = m : ∀αs.Σ1′→⋯→Σn′→Ξ and 〚pi〛 = mi : Σi  and (Σ1,…,Σn)≤∃αs.(Σ1′,…,Σn′) ↑ τs ⇝ fs
moduleApp :: ToF m
             => Path
             -> [Path]
             -> m (F.AbstractSig, F.Term)
moduleApp pfn pargs = do
  (semFn, mfn) <- modulePath pfn
  (argSigs, margs) <- mapAndUnzipM modulePath pargs
  case semFn of
   F.FunctorSem bnd ->
     U.lunbind bnd $ \(tvks, F.SemanticFunctor paramSigs sigResult) -> do
       let alphas = map fst tvks
       (paramSigs', taus) <- F.matchSubsts argSigs (alphas, paramSigs)
       coercions <- zipWithM F.sigSubtyping argSigs paramSigs'
       let
         m = (F.pApps mfn taus) `F.apps` (zipWith F.applyCoercion coercions margs)
         s = U.substs (zip alphas taus) sigResult
       return (s, m)
   _ -> throwError "internal failure: ToF.moduleApp expected a functor"

-- | Translation declarations.
-- This is a bit different from how F-ing modules does it in order to avoid producing quite so many
-- administrative redices, at the expense of being slightly more complex.
--
-- So the idea is that each declaration is going to produce two
-- things: A term with a hole and a description of the extra variable
-- bindings that it introduces in the scope of the hole.
--
-- For example, a type alias "type β = τ" will produce the term
--    let xβ = ↓[τ] in •   and the description {user field β : [τ]} ⇝ {user field β = xβ}
-- The idea is that the "SigSummary" part of the description is the abstract semantic signature of the
-- final structure in which this declaration appears, and the field↦term part is the record value that
-- will be produced.
--
-- For nested submodules we'll have to do a bit more work in order to
-- extrude the scope of the existential variables (ie, the term with
-- the hole is an "unpacks" instead of a "let"), but it's the same
-- idea.
--
-- For value bindings we go in two steps: the signature (which was inserted by the type checker if omitted)
-- just extends the SigSummary, while the actual definition extends the record.
-- TODO: (This gets mutually recursive functions wrong.  Need a letrec form in fomega)
declarations :: ToF m
                => ModuleKind
                -> [Decl]
                -> (ModSummary -> m ans)
                -> m ans
declarations _mk [] kont = kont mempty 
declarations mk (d:ds) kont = let
  kont1 out1 = declarations mk ds $ \outs -> kont $ out1 <> outs
  in case d of
      ValueDecl f vd -> valueDecl mk f vd kont1
      SubmoduleDefn f me -> submoduleDefn mk f me kont1
      SampleModuleDefn f me -> do
        when (mk /= ModelMK) $
          throwError "internal error: ToF.declarations SampleModuleDecl in a module"
        sampleModuleDefn f me kont1
      TypeAliasDefn f al -> typeAliasDefn mk f al kont1
      ImportDecl p ->
        throwError "internal error: ToF.declarations ImportDecl should have been desugared by the Insomnia typechecker"
        {- importDecl p kont1 -}
      TypeDefn f td -> typeDefn f (U.s2n f) td kont1

-- | In Insomnia, the typechecker changed the import declaration into a
-- sequence of declarations.  But we could actually support it
-- natively in the translation here, if we wanted.  In fact, in the
-- F-ing modules paper, "include M" is a primitive construct and we
-- could use it to explain, for example, how data types work.  (There
-- are differences here. In F-ing modules, the include takes a module
-- expression, not a path, as an argument, and consequently it would
-- require unpacking an abstract sig, but we already have all the
-- functions to do that correctly, anyway.)
importDecl :: ToF m
              => Path
              -> (ModSummary -> m ans)
              -> m ans
importDecl importPath kont = do
  (semImp, m) <- modulePath importPath
  case semImp of
   F.ModSem fsigs -> do
     fsems <- forM fsigs $ \(f, sem) ->
       case f of
        F.FUser fld -> return (fld, sem)
        _ -> throwError "internal error: ToF.importDecl expected a module of user fields"
     withFreshName "imp" $ \ ximp -> do
       let
         fs = map fst fsems
         impHole = Endo (F.Let . U.bind (ximp, U.embed m))
         fxs = map (\f -> (f, U.s2n f)) fs
         holes = map (\(f, x) ->
                       Endo (F.Let . U.bind (x, U.embed $ F.Proj (F.V ximp) (F.FUser f))))
                 fxs
         sigSummary = ([], fsigs)
         xtms = map (\(f, x) -> (F.FUser f, F.V x)) fxs
         coord = zipWith (\(f, x) (_f, sem) -> (f, x, sem)) fxs fsems
         hole = impHole <> mconcat holes
         thisOne = (sigSummary, xtms, hole)
       -- XXX: need to add everything in the sig to the environment
       local (extendEnvForImports coord) $
         kont thisOne
   _ -> throwError "internal error: ToF.importDecl expected a module path"

extendEnvForImports :: [(Field, F.Var, F.SemanticSig)]
                       -> Env
                       -> Env
extendEnvForImports [] = id
extendEnvForImports (c:coord) =
  extendEnvForImport c
  . extendEnvForImports coord
  where
    extendEnvForImport :: (Field, F.Var, F.SemanticSig) -> Env -> Env
    extendEnvForImport (f, x, sem) =
      let
        addToModEnv = modEnv %~ M.insert (U.s2n f) (sem, x)
        addToTyConEnv = tyConEnv %~ M.insert (U.s2n f) sem
      in case sem of
       F.ValSem {} -> valEnv %~ M.insert (U.s2n f) (x, StructureTermVar sem)
       F.TypeSem {} -> addToTyConEnv
       F.SigSem absSig -> error "internal error: ToF.extendEnvForImports Insomnia doesn't have local signature definitions, this unexpected."
       F.DataSem {} -> addToTyConEnv
       F.ConSem {} -> valConEnv %~ M.insert (U.s2n f) (x, F.FUser f, error "import con sem")
       F.ModSem {} -> addToModEnv
       F.FunctorSem {} -> addToModEnv
       F.ModelSem {} -> addToModEnv


typeAliasDefn :: ToF m
                 => ModuleKind
                 -> Field
                 -> TypeAlias
                 -> (ModSummary -> m ans)
                 -> m ans
typeAliasDefn _mk f (TypeAlias bnd) kont =
  U.lunbind bnd $ \ (tvks, rhs) -> do
    (tlam, tK) <- withTyVars tvks $ \tvks' -> do
      (rhs', kcod) <- type' rhs
      return (F.tLams tvks' rhs', F.kArrs (map snd tvks') kcod)
    let tsig = F.TypeSem tlam tK
        tc = U.s2n f :: TyConName
        xc = U.s2n f :: F.Var
    msig <- F.typeSemTerm tlam tK
    let
      mr = F.Record [(F.FType, msig)]
      mhole = Endo $ F.Let . U.bind (xc, U.embed mr)
      thisOne = ((mempty, [(F.FUser f, tsig)]),
                 [(F.FUser f, F.V xc)],
                 mhole)
    local (tyConEnv %~ M.insert tc tsig) $
      kont thisOne

submoduleDefn :: ToF m
                 => ModuleKind
                 -> Field
                 -> ModuleExpr
                 -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
                 -> m ans
submoduleDefn _mk f me kont = do
  let modId = U.s2n f
  (F.AbstractSig bnd, msub) <- moduleExpr me
  U.lunbind bnd $ \(tvks, modsig) -> do
    let xv = U.s2n f
    local (modEnv %~ M.insert modId (modsig, xv)) $ do
      let tvs = map fst tvks
      munp <- F.unpacksM tvs xv
      let m = Endo $ munp msub
          thisOne = ((tvks, [(F.FUser f, modsig)]),
                     [(F.FUser f, F.V xv)],
                     m)
      kont thisOne

sampleModuleDefn :: ToF m
                    => Field
                    -> ModuleExpr
                    -> (ModSummary -> m ans)
                    -> m ans
sampleModuleDefn f me kont = do
  let modId = U.s2n f
  (F.AbstractSig bndMdl, msub) <- moduleExpr me
  bnd <- U.lunbind bndMdl $ \(tvNull, semMdl) ->
    case (tvNull, semMdl) of
     ([], F.ModelSem (F.AbstractSig bnd)) -> return bnd
     _ -> throwError "internal error: ToF.sampleModelDefn expected a model with no applicative tyvars"
  U.lunbind bnd $ \(tvks, modSig) -> do
    let xv = U.s2n f
    local (modEnv %~ M.insert modId (modSig, xv)) $ do
      munp <- F.unpacksM (map fst tvks) xv
      let m = Endo $ F.LetSample . U.bind (xv, U.embed msub) . munp (F.V xv)
          thisOne = ((tvks, [(F.FUser f, modSig)]),
                     [(F.FUser f, F.V xv)],
                     m)
      kont thisOne

valueDecl :: ToF m
             => ModuleKind
             -> Field
             -> ValueDecl
             -> (ModSummary -> m ans)
             -> m ans
valueDecl mk f vd kont =
  let v = U.s2n f :: Var
  in case vd of
   SigDecl _stoch ty -> do
     (ty', _k) <- type' ty
     let vsig = F.ValSem ty'
         xv = U.s2n f :: F.Var
     tr <- F.embedSemanticSig vsig
     let thisOne = ((mempty, [(F.FUser f, vsig)]),
                    mempty,
                    mempty)
     local (valEnv %~ M.insert v (xv, StructureTermVar vsig))
       $ U.avoid [U.AnyName v]
       $ kont thisOne
   FunDecl e -> do
     mt <- view (valEnv . at v)
     (xv, sem) <- case mt of
       Just (xv, StructureTermVar sem) -> return (xv, sem)
       _ -> throwError "internal error: ToF.valueDecl FunDecl did not find type declaration for field"
     ty <- matchSemValRecord sem
     m <- tyVarsAbstract ty $ \tvks _ty' -> do
       m_ <- expr e
       return $ F.pLams tvks m_
     let
       mr = F.Record [(F.FVal, m)]
       mhole = Endo $ F.Let . U.bind (xv, U.embed mr)
       thisOne = (mempty,
                  [(F.FUser f, F.V xv)],
                  mhole)
     kont thisOne
   SampleDecl e -> do
     when (mk /= ModelMK) $
       throwError "internal error: ToF.valueDecl SampleDecl in a module"
     simpleValueBinding F.LetSample f v e kont
   ParameterDecl e -> do
     when (mk /= ModuleMK) $
       throwError "internal error: ToF.valueDecl ParameterDecl in a model"
     simpleValueBinding F.Let f v e kont
   ValDecl e -> throwError ("internal error: unexpected ValDecl in ToF.valueDecl;"
                      ++" Insomnia typechecker should have converted into a SampleDecl or a ParameterDecl")
   TabulatedSampleDecl tabfun -> throwError "unimplemented ToF.valueDecl TabulatedSampelDecl"
   
simpleValueBinding :: ToF m
                      => (U.Bind (F.Var, U.Embed F.Term) F.Term -> F.Term)
                      -> Field
                      -> Var
                      -> Expr
                      -> (ModSummary -> m ans)
                      -> m ans
simpleValueBinding mkValueBinding f v e kont = do
  mt <- view (valEnv . at v)
  (xv, _prov) <- case mt of
    Nothing -> throwError "internal error: ToF.valueDecl SampleDecl did not find and type declaration for field"
    Just xty -> return xty
  m <- expr e
  let
    mhole body =
      mkValueBinding $ U.bind (xv, U.embed m)
      $ F.Let $ U.bind (xv, U.embed $ F.Record [(F.FVal, F.V xv)])
      $ body
    thisOne = (mempty,
               [(F.FUser f, F.V xv)],
               Endo mhole)
  kont thisOne




matchSemValRecord :: MonadError String m => F.SemanticSig -> m F.Type
matchSemValRecord (F.ValSem t) = return t
matchSemValRecord _ = throwError "internal error: expected a semantic object of a value binding"

tyVarsAbstract :: ToF m => F.Type -> ([(F.TyVar, F.Kind)] -> F.Type -> m r) -> m r
tyVarsAbstract t_ kont_ = tyVarsAbstract' t_ (\tvks -> kont_ (appEndo tvks []))
  where
    tyVarsAbstract' :: ToF m => F.Type -> (Endo [(F.TyVar, F.Kind)] -> F.Type -> m r) -> m r
    tyVarsAbstract' t kont =
      case t of
       F.TForall bnd ->
         U.lunbind bnd $ \((tv', U.unembed -> k), t') -> do
           let tv = (U.s2n $ U.name2String tv') :: TyVar
           id {- U.avoid [U.AnyName tv] -}
             $ local (tyVarEnv %~ M.insert tv (tv', k))
             $ tyVarsAbstract' t' $ \tvks t'' ->
             kont (tvks <> Endo ((tv', k):)) t''
       _ -> kont mempty t
             

modulePath :: ToF m => Path
              -> m (F.SemanticSig, F.Term)
modulePath = let
  rootLookup modId = do
    ma <- view (modEnv . at modId)
    case ma of
     Nothing -> throwError "unexpected failure in ToF.modulePath - unbound module identifier"
     Just (sig, x) -> return (sig, F.V x)
  in
   followUserPathAnything rootLookup



