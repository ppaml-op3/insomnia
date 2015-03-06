-- | Encoding of the Insomnia module calculus in System FΩ ala "F-ing
-- Modules".
--
-- We proceed in two steps: we translate module types into "semantic
-- signatures" which we then embed in FΩ.  Modules turn out to be
-- terms of the embedded types corresponding to their signatures.  The
-- key "trick" is that generativity is modeled by packing existential
-- types, and dependency (of later module components on prior ones) is
-- modeled by hoisting the scope of the existentials to enclose the
-- definition and the subsequent dependencies.
--
-- In this encoding, models end up encoding as something like "Dist
-- (∃α. τ)" where Dist is the probability distribution monad and τ is
-- the encoding of the underlying structure.  (One could also imagine
-- "∃α. Dist τ" which would correspond to all samples from a
-- distribution sharing the identity of their abstract types.  That is
-- not what we do in Insomnia, however.)
{-# LANGUAGE ViewPatterns,
      FlexibleContexts, FlexibleInstances, TypeSynonymInstances
  #-}
module Insomnia.ToF (Insomnia.ToF.Env.runToFM, moduleExpr, moduleType) where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Data.List as List
import Data.Monoid (Monoid(..), (<>), Endo(..))
import Data.Typeable (Typeable)
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh, Embed)
import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

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
import Insomnia.ToF.Type
import Insomnia.ToF.Pattern
import Insomnia.ToF.Expr

---------------------------------------- Module Types


moduleType :: ToF m => ModuleType -> m F.AbstractSig
moduleType modTy_ =
  case modTy_ of
   SigMT (SigV s ModuleMK) ->
     signature s
   SigMT (SigV s ModelMK) ->
     model s
   IdentMT sigId -> do
     ma <- view $ sigEnv . at sigId
     case ma of
      Nothing -> fail "unexpected ToF.moduleTyp' sig lookup returned Nothing"
      Just absSig -> return absSig
   WhereMT modTy whereClause -> do
     abstr <- moduleType modTy
     patchWhereClause abstr whereClause
   FunMT bnd -> do
     functor bnd

-- ∃ αs:κs . fs:Σs
type SigSummary = ([(F.TyVar, Embed F.Kind)], [(F.Field, F.SemanticSig)])

functor :: ToF m
           => (U.Bind (Telescope (FunctorArgument ModuleType)) ModuleType)
           -> m F.AbstractSig
functor bnd =
  U.lunbind bnd $ \(teleArgs, body) ->
  withFunctorArguments teleArgs $ \(abstr, sigArgs) -> do
    abstrSigBody <- moduleType body
    let
      fctr = F.SemanticFunctor (map snd sigArgs) abstrSigBody
      s =  F.FunctorSem $ U.bind abstr fctr
    return $ F.AbstractSig $ U.bind [] s

withFunctorArguments :: ToF m =>
                        Telescope (FunctorArgument ModuleType)
                        -> (([(F.TyVar, Embed F.Kind)],
                             [(F.Var, F.SemanticSig)])
                            -> m r)
                        -> m r
withFunctorArguments tele kont =
  case tele of
   NilT -> kont mempty
   ConsT (U.unrebind -> (arg, teleArgs)) ->
     withFunctorArgument arg $ \(abstArg, argSem) ->
     withFunctorArguments teleArgs $ \(abstArgs, argsSem) ->
     kont (abstArg <> abstArgs, argSem:argsSem)

withFunctorArgument :: ToF m
                       => FunctorArgument ModuleType
                       -> (([(F.TyVar, Embed F.Kind)],
                            (F.Var, F.SemanticSig))
                           -> m r)
                       -> m r
withFunctorArgument (FunctorArgument argId _modK (U.unembed -> modTy)) kont =
  withFreshName (U.name2String argId) $ \modVar -> do
    (F.AbstractSig bnd) <- moduleType modTy
    U.lunbind bnd $ \(abstrs, modSig) ->
      local (modEnv %~ M.insert argId (modSig, modVar))
      $ kont (abstrs, (modVar, modSig))
  

patchWhereClause :: ToF m => F.AbstractSig -> WhereClause -> m F.AbstractSig
patchWhereClause (F.AbstractSig bnd) (WhereTypeCls path rhsTy) = do
  (rhsTy', _k) <- type' rhsTy
  U.lunbind bnd $ \(abstr, modSem) -> do
    tSem <- followTypePath modSem path
    case tSem of
     (F.TypeSem (F.TV a) _k') -> do
       abstrRest <- dropVarFromAbstrList abstr a
       let modSem' = U.subst a rhsTy' modSem'
       return $ F.AbstractSig $ U.bind abstrRest modSem'
     _ -> fail ("patchWhereClause: expected where clause to pick out "
                ++ " a type variable in the semantic sig")

dropVarFromAbstrList :: (U.Alpha a, Monad m) => [(a, b)] -> a -> m [(a, b)]
dropVarFromAbstrList vs v =
  case List.partition (\(v',_) -> U.aeq v v') vs of
   ([_], rest) -> return rest
   _ -> fail "dropVarFromAbstrList expected exactly one type variable to match"

followTypePath :: ToF m => F.SemanticSig -> (U.Bind Identifier TypePath) -> m F.SemanticSig
followTypePath mod0 bnd =
  U.lunbind bnd $ \(dkId, TypePath modsPath typeField) ->
  withFreshName (U.name2String dkId) $ \x ->
    liftM fst $ followUserPathAnything (const $ return (mod0, F.V x)) (ProjP modsPath typeField)

  
mkAbstractModuleSig :: SigSummary
                       -> F.AbstractSig
mkAbstractModuleSig (tvks, sig) =
  F.AbstractSig $ U.bind tvks $ F.ModSem sig

signature :: ToF m => Signature -> m F.AbstractSig
signature = liftM mkAbstractModuleSig . signature'

model :: ToF m => Signature -> m F.AbstractSig
model sig = do
  abstr <- signature sig
  let s = F.ModelSem abstr
  return $ F.AbstractSig $ U.bind [] s

signature' :: ToF m => Signature -> m SigSummary
signature' UnitSig = return mempty
signature' (ValueSig f t rest) = do
  (t', _) <- type' t
  let s = ([], [(F.FUser f, F.ValSem t')])
  rest' <- signature' rest
  return $ s <> rest'
signature' (TypeSig f bnd) =
  U.lunbind bnd $ \((con, U.unembed -> tsd), rest) ->
  typeSigDecl f con tsd $ signature' rest
signature' (SubmoduleSig f bnd) =
  withFreshName f $ \x -> 
  U.lunbind bnd $ \((subModId, U.unembed -> modTy), rest) ->
  submodule f modTy $ \subSig -> local (modEnv %~ M.insert subModId (subSig, x)) (signature' rest)

submodule :: ToF m => Field -> ModuleType -> (F.SemanticSig -> m SigSummary) -> m SigSummary
submodule f modTy kont = do
  (F.AbstractSig bnd) <- moduleType modTy
  U.lunbind bnd $ \(abstr, sig) -> do
    let s = (abstr, [(F.FUser f, sig)])
    rest' <- kont sig
    return $ s <> rest'

typeSigDecl :: ToF m
               => Field
               -> TyConName
               -> TypeSigDecl
               -> m SigSummary
               -> m SigSummary
typeSigDecl f selfTc tsd kont = do           
  case tsd of
   AliasTypeSigDecl alias -> do
     sig <- typeAlias alias
     rest' <- local (tyConEnv %~ M.insert selfTc sig) kont
     let
       s = ([], [(F.FUser f, sig)])
     return $ s <> rest'
   AbstractTypeSigDecl k ->
     withFreshName f $ \tv -> do
       k' <- kind k
       let sig = F.TypeSem (F.TV tv) k'
       rest' <- local (tyConEnv %~ M.insert selfTc sig) kont
       let
         s = ([(tv, U.embed k')], [(F.FUser f, sig)])
       return $ s <> rest'
   ManifestTypeSigDecl td -> do
     typeDefn f selfTc td $ \(s, _m, _mhole) -> do
       rest' <- kont
       return $ s <> rest'

typeDefn :: ToF m
            => Field
            -> TyConName
            -> TypeDefn
            -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
            -> m ans
typeDefn f selfTc td_ kont =
  case td_ of
   EnumDefn numeracy ->
     withFreshName "Δ" $ \enumTyModV ->
     withFreshName ("δ" ++ show numeracy) $ \tv -> do
       let
         -- enum becomes: δ → (∀ α : ⋆ . α → (δ → α) → α)
         -- that is, it's isomorphic to primitive recursion over a nat.
         tFold = let a = U.s2n "α"
                 in (F.TForall $ U.bind (a, U.embed F.KType)
                     $ F.tArrs [F.TV a
                               , F.TV tv `F.TArr` F.TV a
                               ]
                     $ (F.TV a))
         dataSem = F.DataSem (F.TV tv) tFold F.KType
         dataSig = [(F.FUser f, dataSem)]
         abstr = [(tv, U.embed F.KType)]
       dataTy <- F.embedSemanticSig dataSem
       let dataModSem = F.ModSem [(F.FUser f, dataSem)]
           dataModAbs = F.AbstractSig $ U.bind [(tv, U.embed F.KType)] dataModSem
       dataModTy <- F.embedAbstractSig dataModAbs
       let dataModTm = F.Assume dataModTy
           unpackHole = Endo (F.Unpack . U.bind (tv, enumTyModV, U.embed dataModTm))
           xenum = U.s2n f
           dTm = [(F.FUser f, F.V xenum)]
           dHole = Endo (F.Let . U.bind (xenum, U.embed $ F.Proj (F.V enumTyModV) (F.FUser f)))
           absSig = (abstr, dataSig)
           thisOne = (absSig, dTm, unpackHole <> dHole)
       local (tyConEnv %~ M.insert selfTc dataSem)
         $ kont thisOne
   DataDefn bnd ->
     U.lunbind bnd $ \(tvks, constrs) ->
     withTyVars tvks $ \tvks' ->
     withFreshName "Δ" $ \dataTyModV ->
     withFreshName "δ" $ \tv -> do
       let kdoms = map snd tvks'
           k = kdoms `F.kArrs` F.KType
       local (tyConEnv %~ M.insert selfTc (F.TypeSem (F.TV tv) k)) $ do
         -- fully apply data type abstract var to parameter vars
         let tCod = (F.TV tv) `F.tApps` map (F.TV . fst) tvks'
         (constrSems, summands) <- liftM (unzip . map (\(f,y,z) -> ((f,y), (F.FUser f, z))))
                                   $ mapM (mkConstr tvks' tCod)
                                   $ constrs
         let tConc = F.tLams tvks' $ F.TSum summands
             cSems = map (\(f, sem) -> (U.s2n f, sem)) constrSems
             constrSigs = map (\(f, sem) -> (F.FUser f, sem)) constrSems
             dataSem = F.DataSem (F.TV tv) tConc k
             dataSig = (F.FUser f, dataSem)
             abstr = [(tv, U.embed k)]
         dataTy <- F.embedSemanticSig dataSem
         let dataModSem = F.ModSem $ (F.FUser f, dataSem) : constrSigs
             dataModAbs = F.AbstractSig $ U.bind [(tv, U.embed k)] dataModSem
         dataModTy <- F.embedAbstractSig dataModAbs
         let dataModTm = F.Assume dataModTy -- not specifying how datatypes are implemented.
             -- unpack δ,Δ = assume { D = {data = ...}, C1 = {con = ...}, ..., CN = {con = ...}} in []
             unpackHole = Endo (F.Unpack . U.bind (tv, dataTyModV, U.embed dataModTm))
         (fxvs, conholes) <- liftM unzip $ forM constrSems $ \(f, sem) -> do
           ty <- F.embedSemanticSig sem
           let
             xv = U.s2n f :: F.Var
             mhole = Endo (F.Let . U.bind (xv, U.embed $ F.Proj (F.V dataTyModV) (F.FUser f)))
           return ((f, xv), mhole)
         let
           xdata = U.s2n f
           dTm = (F.FUser f, F.V xdata)
           dHole = Endo (F.Let . U.bind (xdata, U.embed $ F.Proj (F.V dataTyModV) (F.FUser f)))
           conTms = map (\(f, x) -> (F.FUser f, F.V x)) fxvs
           conVs = M.fromList $ map (\(f, x) -> (U.s2n f, x)) fxvs
           absSig = (abstr, dataSig : constrSigs)
           thisOne = (absSig, dTm : conTms, unpackHole <> dHole <> mconcat conholes)
         local (tyConEnv %~ M.insert selfTc dataSem)
           . local (valConEnv %~ M.union conVs)
           $ kont thisOne
  where
    mkConstr :: ToF m => [(F.TyVar, F.Kind)] -> F.Type -> ConstructorDef -> m (Field, F.SemanticSig, F.Type)
    mkConstr tvks tCod (ConstructorDef cname tDoms) = do
      (tDoms', _) <- liftM unzip $ mapM type' tDoms
      let f = U.name2String cname
          t = F.tForalls tvks $ tDoms' `F.tArrs` tCod
          tsummand = F.tupleT tDoms'
      return (f, F.ConSem t, tsummand)

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
      (taus, f) <- do
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
        finalOut = F.Return $ F.packs taus (F.App f (F.V w)) packsAnnotation
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
    (taus, f) <- do
      (sig2, taus) <- F.matchSubst sigma xi
      coercion <- F.sigSubtyping sigma sig2
      return (taus, coercion)
    z1 <- U.lfresh (U.s2n "z")
    let
      packedTys = (map (F.TV . fst) betas)
                  ++ taus
    (xi', bdy) <- U.lunbind xiBnd $ \(deltas,sigma2) -> do
      sigma2emb <- F.embedSemanticSig sigma2
      let bdy = F.packs packedTys (F.App f $ F.V z1) (betas++deltas, sigma2emb)
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
         m = (F.pApps mfn taus) `F.apps` (zipWith F.App coercions margs)
         s = U.substs (zip alphas taus) sigResult
       return (s, m)
   _ -> fail "internal failure: ToF.moduleApp expected a functor"

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
                -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
                -> m ans
declarations _mk [] kont = kont mempty 
declarations mk (d:ds) kont = let
  kont1 out1 = declarations mk ds $ \outs -> kont $ out1 <> outs
  in case d of
      ValueDecl f vd -> valueDecl mk f vd kont1
      SubmoduleDefn f me -> submoduleDefn mk f me kont1
      SampleModuleDefn f me -> do
        when (mk /= ModelMK) $
          fail "internal error: ToF.declarations SampleModuleDecl in a module"
        sampleModuleDefn f me kont1
      TypeAliasDefn f al -> typeAliasDefn mk f al kont1
      ImportDecl p ->
        fail "internal error: ToF.declarations ImportDecl should have been desugared by the Insomnia typechecker"
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
              -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
              -> m ans
importDecl importPath kont = do
  (semImp, m) <- modulePath importPath
  case semImp of
   F.ModSem fsigs -> do
     fsems <- forM fsigs $ \(f, sem) ->
       case f of
        F.FUser fld -> return (fld, sem)
        _ -> fail "internal error: ToF.importDecl expected a module of user fields"
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
   _ -> fail "internal error: ToF.importDecl expected a module path"

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
       F.ConSem {} -> valConEnv %~ M.insert (U.s2n f) x
       F.ModSem {} -> addToModEnv
       F.FunctorSem {} -> addToModEnv
       F.ModelSem {} -> addToModEnv


typeAliasDefn :: ToF m
                 => ModuleKind
                 -> Field
                 -> TypeAlias
                 -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
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
                    -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
                    -> m ans
sampleModuleDefn f me kont = do
  let modId = U.s2n f
  (F.AbstractSig bndMdl, msub) <- moduleExpr me
  bnd <- U.lunbind bndMdl $ \(tvNull, semMdl) ->
    case (tvNull, semMdl) of
     ([], F.ModelSem (F.AbstractSig bnd)) -> return bnd
     _ -> fail "internal error: ToF.sampleModelDefn expected a model with no applicative tyvars"
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
             -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
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
       _ -> fail "internal error: ToF.valueDecl FunDecl did not find type declaration for field"
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
       fail "internal error: ToF.valueDecl SampleDecl in a module"
     simpleValueBinding F.LetSample f v e kont
   ParameterDecl e -> do
     when (mk /= ModuleMK) $
       fail "internal error: ToF.valueDecl ParameterDecl in a model"
     simpleValueBinding F.Let f v e kont
   ValDecl e -> fail ("internal error: unexpected ValDecl in ToF.valueDecl;"
                      ++" Insomnia typechecker should have converted into a SampleDecl or a ParameterDecl")
   TabulatedSampleDecl tabfun -> fail "unimplemented ToF.valueDecl TabulatedSampelDecl"
   
simpleValueBinding :: ToF m
                      => (U.Bind (F.Var, U.Embed F.Term) F.Term -> F.Term)
                      -> Field
                      -> Var
                      -> Expr
                      -> ((SigSummary, [(F.Field, F.Term)], Endo F.Term) -> m ans)
                      -> m ans
simpleValueBinding mkValueBinding f v e kont = do
  mt <- view (valEnv . at v)
  (xv, _prov) <- case mt of
    Nothing -> fail "internal error: ToF.valueDecl SampleDecl did not find and type declaration for field"
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




matchSemValRecord :: Monad m => F.SemanticSig -> m F.Type
matchSemValRecord (F.ValSem t) = return t
matchSemValRecord _ = fail "internal error: expected a semantic object of a value binding"

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
     Nothing -> fail "unexpected failure in ToF.modulePath - unbound module identifier"
     Just (sig, x) -> return (sig, F.V x)
  in
   followUserPathAnything rootLookup


---------------------------------------- Core language


