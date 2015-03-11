{-# LANGUAGE ViewPatterns, FlexibleContexts #-}
module Insomnia.ToF.ModuleType where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Except (MonadError(..))
import Data.Monoid (Monoid(..), (<>), Endo(..))
import qualified Data.Map as M
import qualified Data.List as List

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.ModuleType
import Insomnia.TypeDefn
import Insomnia.Types

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Summary
import Insomnia.ToF.Type (kind, type', withTyVars, typeAlias)

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
      Nothing -> throwError "unexpected ToF.moduleTyp' sig lookup returned Nothing"
      Just absSig -> return absSig
   WhereMT modTy whereClause -> do
     abstr <- moduleType modTy
     patchWhereClause abstr whereClause
   FunMT bnd -> do
     functor bnd

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
                        -> (ExposedAbstractSig F.Var -> m r)
                        -> m r
withFunctorArguments tele kont =
  case tele of
   NilT -> kont mempty
   ConsT (U.unrebind -> (arg, teleArgs)) ->
     withFunctorArgument arg $ \(abstArg, argSem) ->
     withFunctorArguments teleArgs $ \(abstArgs, argsSem) ->
     kont (abstArg <> abstArgs, argSem<>argsSem)

withFunctorArgument :: ToF m
                       => FunctorArgument ModuleType
                       -> (ExposedAbstractSig F.Var -> m r)
                       -> m r
withFunctorArgument (FunctorArgument argId _modK (U.unembed -> modTy)) kont =
  withFreshName (U.name2String argId) $ \modVar -> do
    (F.AbstractSig bnd) <- moduleType modTy
    U.lunbind bnd $ \(abstrs, modSig) ->
      local (modEnv %~ M.insert argId (modSig, modVar))
      $ kont (abstrs, [(modVar, modSig)])
  

patchWhereClause :: ToF m => F.AbstractSig -> WhereClause -> m F.AbstractSig
patchWhereClause (F.AbstractSig bnd) (WhereTypeCls path rhsTy) = do
  (rhsTy', _k) <- type' rhsTy
  U.lunbind bnd $ \(abstr, modSem) -> do
    tSem <- followTypePath modSem path
    case tSem of
     (F.TypeSem (F.TV a) _k') -> do
       abstrRest <- dropVarFromAbstrList abstr a
       let modSem' = U.subst a rhsTy' modSem
       return $ F.AbstractSig $ U.bind abstrRest modSem'
     _ -> throwError ("patchWhereClause: expected where clause to pick out "
                ++ " a type variable in the semantic sig")

dropVarFromAbstrList :: (U.Alpha a, MonadError String m, Monad m) => [(a, b)] -> a -> m [(a, b)]
dropVarFromAbstrList vs v =
  case List.partition (\(v',_) -> U.aeq v v') vs of
   ([_], rest) -> return rest
   _ -> throwError "dropVarFromAbstrList expected exactly one type variable to match"

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
            -> (ModSummary -> m ans)
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
       let dtf = F.FUser f
           kdoms = map snd tvks'
           k = kdoms `F.kArrs` F.KType
       local (tyConEnv %~ M.insert selfTc (F.TypeSem (F.TV tv) k)) $ do
         -- fully apply data type abstract var to parameter vars
         let tCod = (F.TV tv) `F.tApps` map (F.TV . fst) tvks'
         (constrSems, summands) <- liftM (unzip . map (\(f,y,z) -> ((f,y), (F.FUser f, z))))
                                   $ mapM (mkConstr dtf tvks' tCod)
                                   $ constrs
         let tConc = F.tLams tvks' $ F.TSum summands
             cSems = map (\(f, sem) -> (U.s2n f, sem)) constrSems
             constrSigs = map (\(f, sem) -> (F.FUser f, sem)) constrSems
             dataSem = F.DataSem (F.TV tv) tConc k
             dataSig = (dtf, dataSem)
             abstr = [(tv, U.embed k)]
         dataTy <- F.embedSemanticSig dataSem
         let dataModSem = F.ModSem $ (dtf, dataSem) : constrSigs
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
           dTm = (dtf, F.V xdata)
           dHole = Endo (F.Let . U.bind (xdata, U.embed $ F.Proj (F.V dataTyModV) (dtf)))
           conTms = map (\(f, x) -> (F.FUser f, F.V x)) fxvs
           conVs = M.fromList $ map (\(f, x) -> (U.s2n f, (x, F.FUser f, xdata))) fxvs
           absSig = (abstr, dataSig : constrSigs)
           thisOne = (absSig, dTm : conTms, unpackHole <> dHole <> mconcat conholes)
         local (tyConEnv %~ M.insert selfTc dataSem)
           . local (valConEnv %~ M.union conVs)
           $ kont thisOne
  where
    mkConstr :: ToF m
                => F.Field
                -> [(F.TyVar, F.Kind)]
                -> F.Type
                -> ConstructorDef
                -> m (Field, F.SemanticSig, F.Type)
    mkConstr dt tvks tCod (ConstructorDef cname tDoms) = do
      (tDoms', _) <- liftM unzip $ mapM type' tDoms
      let f = U.name2String cname
          t = F.tForalls tvks $ tDoms' `F.tArrs` tCod
          tsummand = F.tupleT tDoms'
      return (f, F.ConSem t dt, tsummand)

