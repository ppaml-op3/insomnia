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
import Insomnia.ToF.Type (kind, type', typeAlias)
import Insomnia.ToF.DataType

---------------------------------------- Module Types


moduleType :: ToF m => ModuleType -> m F.AbstractSig
moduleType modTy_ =
  case modTy_ of
   SigMT (SigV s ModuleMK) ->
     signature s
   SigMT (SigV s ModelMK) ->
     model s
   IdentMT (SigIdP sigId) -> do
     ma <- view $ sigEnv . at sigId
     case ma of
      Nothing -> throwError "unexpected ToF.moduleTyp' sig lookup returned Nothing"
      Just absSig -> return absSig
   IdentMT (SigTopRefP topref f) -> do
     m <- view (toplevelEnv . at topref)
     sigTop <- case m of
      Just (sig, _x) -> return sig
      Nothing -> throwError ("unexpected failure in ToF.moduleType: toplevel "
                             ++ show topref ++ " not in environment")
     case sigTop of
      F.ModSem flds -> do
        let p (F.FUser f', _) | f == f' = True
            p _ = False
        case List.find p flds of
         Just (_, (F.SigSem absSig)) -> return absSig
         Just _ -> throwError ("unexpected failure in ToF.moduleType: field "
                               ++ show f ++ " is not a semantic signature")
         Nothing -> throwError ("unexpected failure in ToF.moduleType: field "
                                ++ show f ++ " not found in " ++ show topref)
      _ -> throwError "unexpected failure in followUserPathAnything: not a module record"
        
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
     withFreshName ("δ" ++ show numeracy) $ \dtv -> do
       let
         -- enum becomes: δ ≙ fix λδ:⋆ . {z :  {} ; s : δ }
         -- that is, it's isomorphic to primitive recursion over a nat.
         fs = U.bind []
              [(F.FCon "z", [])
              , (F.FCon "s", [F.TV dtv])]
         dtsem = F.DataTypeSem fs
         dataSem = F.DataSem dtv dtsem F.KType
         abstr = [(dtv, U.embed F.KType)]
         absDataSem = F.AbstractSig $ U.bind abstr dataSem
       absDtTy <- F.embedAbstractSig absDataSem
       let
         dataTyModM = F.Assume absDtTy
         unpackHole = Endo (F.Unpack . U.bind (dtv, enumTyModV, U.embed dataTyModM))
         absSig = (abstr, [(F.FUser f, dataSem)])
         fieldData = [(F.FUser f, F.V enumTyModV)]
         thisOne = (absSig, fieldData, unpackHole)
       local (tyConEnv %~ M.insert selfTc dataSem)
         $ kont thisOne

   DataDefn bnd ->
     datatypeDefinition f selfTc bnd kont
