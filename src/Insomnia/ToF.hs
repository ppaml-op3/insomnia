{-# LANGUAGE ViewPatterns, TemplateHaskell, FlexibleContexts #-}
module Insomnia.ToF where

import Control.Lens
import Control.Monad.Reader
import qualified Data.List as List
import Data.Monoid (Monoid(..), (<>))
import Data.Typeable (Typeable)
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh, Embed)
import qualified Unbound.Generics.LocallyNameless as U

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.Common.ModuleKind
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModuleType

data Env = Env { _tyConEnv :: M.Map TyConName F.SemanticSig
               , _sigEnv   :: M.Map SigIdentifier F.AbstractSig
               , _modEnv   :: M.Map Identifier F.SemanticSig
               , _tyVarEnv :: M.Map TyVar (F.TyVar, F.Kind)
               }

$(makeLenses ''Env)

class (Functor m, LFresh m, MonadReader Env m) => ToF m

moduleType :: ToF m => ModuleType -> m F.AbstractSig
moduleType modTy_ =
  case modTy_ of
   SigMT (SigV s ModuleMK) ->
     signature s
   IdentMT sigId -> do
     ma <- view $ sigEnv . at sigId
     case ma of
      Nothing -> fail "unexpected ToF.moduleTyp' sig lookup returned Nothing"
      Just absSig -> return absSig
   WhereMT modTy whereClause -> do
     abstr <- moduleType modTy
     patchWhereClause abstr whereClause

-- ∃ αs:κs . fs:Σs
type SigSummary = ([(F.TyVar, Embed F.Kind)], [(F.Field, F.SemanticSig)])

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

followTypePath :: LFresh m => F.SemanticSig -> (U.Bind Identifier TypePath) -> m F.SemanticSig
followTypePath mod0 bnd =
  U.lunbind bnd $ \(_, TypePath modsPath typeField) ->
    followUserPathAnything mod0 (ProjP modsPath typeField)

followUserPathAnything :: Monad m => F.SemanticSig -> Path -> m F.SemanticSig
followUserPathAnything mod0 (IdP _) = return mod0
followUserPathAnything mod0 (ProjP path f) = do
  mod1 <- followUserPathAnything mod0 path
  case mod1 of
   (F.ModSem flds) -> do
     let p (F.FUser f', _) | f == f' = True
         p _ = False
     case List.find p flds of
      Just (_, mod2) -> return mod2
      Nothing -> fail "unexpectd failure in followUserPathAnything: field not found"
   _ -> fail "unexpected failure in followUserPathAnything: not a module record"
  
mkAbstractModuleSig :: SigSummary
                       -> F.AbstractSig
mkAbstractModuleSig (tvks, sig) =
  F.AbstractSig $ U.bind tvks $ F.ModSem sig

signature :: ToF m => Signature -> m F.AbstractSig
signature = liftM mkAbstractModuleSig . signature'

signature' :: ToF m => Signature -> m SigSummary
signature' UnitSig = return mempty
signature' (ValueSig f t rest) = do
  (t', _) <- type' t
  let s = ([], [(F.FUser f, F.ValSem t')])
  rest' <- signature' rest
  return $ s <> rest'
signature' (TypeSig f bnd) =
  U.lunbind bnd $ \((con, U.unembed -> tsd), rest) ->
  typeSigDecl f tsd $ \sig -> local (tyConEnv %~ M.insert con sig) (signature' rest)
signature' (SubmoduleSig f bnd) =
  U.lunbind bnd $ \((subModId, U.unembed -> modTy), rest) ->
  submodule f modTy $ \subSig -> local (modEnv %~ M.insert subModId subSig) (signature' rest)

submodule :: ToF m => Field -> ModuleType -> (F.SemanticSig -> m SigSummary) -> m SigSummary
submodule f modTy kont = do
  (F.AbstractSig bnd) <- moduleType modTy
  U.lunbind bnd $ \(abstr, sig) -> do
    let s = (abstr, [(F.FUser f, sig)])
    rest' <- kont sig
    return $ s <> rest'

typeSigDecl :: ToF m
               => Field
               -> TypeSigDecl
               -> (F.SemanticSig -> m SigSummary)
               -> m SigSummary
typeSigDecl f tsd kont = do           
  case tsd of
   AliasTypeSigDecl alias -> do
     sig <- typeAlias alias
     rest' <- kont sig
     let
       s = ([], [(F.FUser f, sig)])
     return $ s <> rest'
   AbstractTypeSigDecl k ->
     withFreshName f $ \tv -> do
       k' <- kind k
       let sig = F.TypeSem (F.TV tv) k'
       rest' <- kont sig
       let
         s = ([(tv, U.embed k')], [(F.FUser f, sig)])
       return $ s <> rest'
   ManifestTypeSigDecl td -> do
     (abstr, sig) <- typeDefn td
     rest' <- kont sig
     let
       s = (abstr, [(F.FUser f, sig)])
     return $ s <> rest'

typeDefn :: ToF m =>  TypeDefn -> m ([(F.TyVar, Embed F.Kind)], F.SemanticSig)
typeDefn td_ =
  case td_ of
   EnumDefn _n -> fail "unimplemented ToF.typeDefn EnumDefn"
   DataDefn bnd ->
     U.lunbind bnd $ \(tvks, constrs) ->
     withTyVars tvks $ \tvks' ->
     withFreshName "<datatype>" $ \tv -> do
       let kdoms = map snd tvks'
           k = kdoms `F.kArrs` F.KType
           abstr = [(tv, U.embed k)]
           -- fully apply data type abstract var to parameter vars
           tCod = (F.TV tv) `F.tApps` map (F.TV . fst) tvks'
       constrSigs <- mapM (mkConstr tvks' tCod) constrs
       let sig = F.ModSem ([(F.FData, F.TypeSem (F.TV tv) k)]
                           ++ constrSigs)
       return (abstr, sig)
  where
    mkConstr :: ToF m => [(F.TyVar, F.Kind)] -> F.Type -> ConstructorDef -> m (F.Field, F.SemanticSig)
    mkConstr tvks tCod (ConstructorDef cname tDoms) = do
      (tDoms', _) <- liftM unzip $ mapM type' tDoms
      let f = U.name2String cname
          t = F.tForalls tvks $ tDoms' `F.tArrs` tCod
      return (F.FCon f, F.ConSem t)
    
typeAlias :: ToF m => TypeAlias -> m F.SemanticSig
typeAlias (TypeAlias bnd) =
  U.lunbind bnd $ \(tvks, t) ->
  withTyVars tvks $ \tvks' -> do
    (t', kcod) <- type' t
    let kdoms = map snd tvks'
        k = kdoms `F.kArrs` kcod
    return $ F.TypeSem t' k

withFreshName :: (Typeable a, ToF m) => String -> (U.Name a -> m r) -> m r
withFreshName s kont = do
  n' <- U.lfresh $ U.s2n s
  U.avoid [U.AnyName n'] $ kont n'

withTyVars :: ToF m => [KindedTVar] -> ([(F.TyVar, F.Kind)] -> m r) -> m r
withTyVars [] kont = kont []
withTyVars ((tv, k):tvks) kont = do
  k' <- kind k
  withFreshName (U.name2String tv) $ \tv' -> 
    local (tyVarEnv %~ M.insert tv (tv', k'))
    $ withTyVars tvks
    $ \rest ->
       kont $ (tv', k') : rest

kind :: Monad m => Kind -> m F.Kind
kind KType = return F.KType
kind (KArr k1 k2) = do
  k1' <- kind k1
  k2' <- kind k2
  return $ F.KArr k1' k2'

type' :: ToF m => Type -> m (F.Type, F.Kind)
type' _ = fail "unimplemented ToF.type'"
