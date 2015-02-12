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
{-# LANGUAGE ViewPatterns, TemplateHaskell,
      FlexibleContexts, FlexibleInstances, TypeSynonymInstances
  #-}
module Insomnia.ToF where

import Control.Lens
import Control.Monad.Reader
import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified Data.List as List
import Data.Monoid (Monoid(..), (<>))
import Data.Typeable (Typeable)
import qualified Data.Map as M

import Unbound.Generics.LocallyNameless (LFresh, Embed)
import qualified Unbound.Generics.LocallyNameless as U

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn
import Insomnia.ModuleType
import Insomnia.Module
import Insomnia.Expr
  
data Env = Env { _tyConEnv :: M.Map TyConName F.SemanticSig
               , _sigEnv   :: M.Map SigIdentifier F.AbstractSig
               , _modEnv   :: M.Map Identifier (F.SemanticSig, F.Var)
               , _tyVarEnv :: M.Map TyVar (F.TyVar, F.Kind)
               , _valEnv    :: M.Map Var (F.Var, F.Type)
               }

$(makeLenses ''Env)

emptyToFEnv :: Env
emptyToFEnv = Env initialTyConEnv mempty mempty mempty mempty

initialTyConEnv :: M.Map TyConName F.SemanticSig
initialTyConEnv = M.fromList [(U.s2n "->",
                               F.TypeSem arrowLam ([F.KType, F.KType] `F.kArrs` F.KType))
                             ]
  where
    arrowLam = F.TLam $ U.bind (alpha, U.embed F.KType) $
               F.TLam $ U.bind (beta, U.embed F.KType) $
               F.TArr (F.TV alpha) (F.TV beta)
    alpha = U.s2n "α"
    beta = U.s2n "β"

class (Functor m, LFresh m, MonadReader Env m, MonadPlus m) => ToF m

type ToFM = MaybeT (ReaderT Env U.LFreshM)

instance ToF ToFM

runToFM :: ToFM a -> a
runToFM m =
  case U.runLFreshM (runReaderT (runMaybeT m) emptyToFEnv) of
   Nothing -> error "unexpected failure in ToF.runToFM"
   Just a -> a

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
      fctr = F.SemanticFunctor sigArgs abstrSigBody
      s =  F.FunctorSem $ U.bind abstr fctr
    return $ F.AbstractSig $ U.bind [] s

withFunctorArguments :: ToF m =>
                        Telescope (FunctorArgument ModuleType)
                        -> (([(F.TyVar, Embed F.Kind)],
                             [F.SemanticSig])
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
                            F.SemanticSig)
                           -> m r)
                       -> m r
withFunctorArgument (FunctorArgument argId _modK (U.unembed -> modTy)) kont =
  withFreshName (U.name2String argId) $ \modVar -> do
    (F.AbstractSig bnd) <- moduleType modTy
    U.lunbind bnd $ \(abstrs, modSig) ->
      local (modEnv %~ M.insert argId (modSig, modVar))
      $ kont (abstrs, modSig)
  

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

followUserPathAnything :: Monad m =>
                          (Identifier -> m (F.SemanticSig, F.Term))
                          -> Path -> m (F.SemanticSig, F.Term)
followUserPathAnything rootLookup (IdP ident) = rootLookup ident
followUserPathAnything rootLookup (ProjP path f) = do
  (mod1, m) <- followUserPathAnything rootLookup path
  case mod1 of
   (F.ModSem flds) -> do
     let p (F.FUser f', _) | f == f' = True
         p _ = False
     case List.find p flds of
      Just (_, mod2) -> return (mod2, F.Proj m (F.FUser f))
      Nothing -> fail "unexpectd failure in followUserPathAnything: field not found"
   _ -> fail "unexpected failure in followUserPathAnything: not a module record"
  
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
  typeSigDecl f tsd $ \sig -> local (tyConEnv %~ M.insert con sig) (signature' rest)
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
withTyVars (tvk:tvks) kont =
  withTyVar tvk $ \tvk' -> 
  withTyVars tvks $ \tvks' ->
  kont $ tvk':tvks'

withTyVar :: ToF m => KindedTVar -> ((F.TyVar, F.Kind) -> m r) -> m r
withTyVar (tv, k) kont = do
  k' <- kind k
  withFreshName (U.name2String tv) $ \tv' -> 
    local (tyVarEnv %~ M.insert tv (tv', k'))
    $ kont $ (tv', k')

kind :: Monad m => Kind -> m F.Kind
kind KType = return F.KType
kind (KArr k1 k2) = do
  k1' <- kind k1
  k2' <- kind k2
  return $ F.KArr k1' k2'

type' :: ToF m => Type -> m (F.Type, F.Kind)
type' t_ =
  case t_ of
   TV tv -> do
     mv <- view (tyVarEnv . at tv)
     case mv of
      Just (tv', k') -> return (F.TV tv', k')
      Nothing -> fail "ToF.type' internal error: type variable not in environment"
   TUVar _ -> fail "ToF.type' internal error: unexpected unification variable"
   TC tc -> typeConstructor tc
   TAnn t k -> do
     (t', _) <- type' t
     k' <- kind k
     return (t', k')
   TApp t1 t2 -> do
     (t1', karr) <- type' t1
     (t2', _) <- type' t2
     case karr of
      (F.KArr _ k2) -> return (F.TApp t1' t2', k2)
      F.KType -> fail "ToF.type' internal error: unexpected KType in function position of type application"
   TForall bnd ->
     U.lunbind bnd $ \((tv, k), tbody) -> 
     withTyVar (tv,k) $ \(tv', k') -> do
       (tbody', _) <- type' tbody
       let
         tall = F.TForall $ U.bind (tv', U.embed k') $ tbody'
       return (tall, F.KType)
   TRecord (Row lts) -> do
     fts <- forM lts $ \(l, t) -> do
       (t', _) <- type' t
       return (F.FUser $ labelName l, t')
     return (F.TRecord fts, F.KType)

typeConstructor :: ToF m => TypeConstructor -> m (F.Type, F.Kind)
typeConstructor (TCLocal tc) = do
  ma <- view (tyConEnv . at tc)
  e <- view tyConEnv
  case ma of
   Just (F.TypeSem t k) -> return (t, k)
   Just f -> fail $ "ToF.typeConstructor: wanted a TypeSem, got a " ++ show f
   Nothing -> fail $ "ToF.typeConstructor: tyConEnv did not contain a TypeSem for a local type constructor: " ++ show tc ++ " in " ++ show e
typeConstructor (TCGlobal (TypePath p f)) = do
  let
    findIt ident = do
      ma <- view (modEnv . at ident)
      case ma of
       Just (sig, x) -> return (sig, F.V x)
       Nothing -> fail "ToF.typeConstructor: type path has unbound module identifier at the root"
  (s, _m) <- followUserPathAnything findIt (ProjP p f)
  case s of
   F.TypeSem t k -> return (t, k)
   _ -> fail "ToF.typeConstructor: type path maps to non-type semantic signature"
  
                      
---------------------------------------- Modules

moduleExpr :: ToF m => ModuleExpr -> m (F.AbstractSig, F.Term)
moduleExpr mdl_ =
  case mdl_ of
   ModuleStruct mdl -> structure mdl
   ModuleSeal {} -> fail "unimplemented ToF.moduleExpr ModuleSeal"
   ModuleAssume {} -> fail "unimplemented ToF.moduleExpr ModuleAssume"
   ModuleId p -> do
     (sig, m) <- modulePath p
     return (F.AbstractSig $ U.bind [] sig, m)
   ModuleFun {} -> fail "unimplemented ToF.moduleExpr ModuleFun"
   ModuleApp {} -> fail "unimplemented ToF.moduleExpr ModuleApp"
   ModuleModel {} -> fail "unimplemented ToF.moduleExpr ModuleModel"

structure :: ToF m => Module -> m (F.AbstractSig, F.Term)
structure (Module decls) = do
  declarations decls $ \(summary@(tvks,_), fields) -> do
    let absSig = mkAbstractModuleSig summary
    ty <- F.embedAbstractSig absSig
    let r = F.Record fields
        m = F.packs (map (F.TV . fst) tvks) r (tvks, ty)
    return (absSig, m)

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
declarations :: ToF m => [Decl] -> ((SigSummary, [(F.Field, F.Term)]) -> m (a, F.Term)) -> m (a, F.Term)
declarations [] kont = kont ((mempty, mempty), mempty)
declarations (d:ds) kont =
  case d of
   ValueDecl f vd -> valueDecl f vd ds kont
   SubmoduleDefn f me -> submoduleDefn f me ds kont
   SampleModuleDefn {} -> fail "unimplemented ToF.declarations SubmoduleDefn"
   TypeAliasDefn {} -> fail "unimplemented ToF.declarations TypeAliasDefn"
   ImportDecl {} -> fail "unimplemented ToF.declarations ImportDecl"
   TypeDefn {} -> fail "unimplemented ToF.declarations TypeDefn"
   

submoduleDefn :: ToF m
                 => Field
                 -> ModuleExpr
                 -> [Decl]
                 -> ((SigSummary, [(F.Field, F.Term)]) -> m (a, F.Term))
                 -> m (a, F.Term)
submoduleDefn f me ds kont = do
  let modId = U.s2n f
  (F.AbstractSig bnd, msub) <- moduleExpr me
  U.lunbind bnd $ \(tvks, modsig) -> do
    let xv = U.s2n f
    local (modEnv %~ M.insert modId (modsig, xv))
      $ declarations ds
      $ \ans -> do
        (a, mstruct) <- kont $ ((tvks, [(F.FUser f, modsig)]), [(F.FUser f, F.V xv)]) <> ans
        let tvs = map fst tvks
        m <- F.unpacks tvs xv msub mstruct
        return (a, m)

valueDecl :: ToF m => Field -> ValueDecl -> [Decl]
             -> ((SigSummary, [(F.Field, F.Term)]) -> m (a, F.Term))
             -> m (a, F.Term)
valueDecl f vd ds kont =
  let v = U.s2n f :: Var
  in case vd of
   SigDecl _stoch ty -> do
     (ty', _k) <- type' ty
     let vsig = F.ValSem ty'
         xv = U.s2n f :: F.Var
     tr <- F.embedSemanticSig vsig
     local (valEnv %~ M.insert v (xv, tr))
       $ U.avoid [U.AnyName v]
       $ declarations ds
       $ \ans ->
          kont $ ((mempty, [(F.FUser f, vsig)]), mempty) <> ans
   FunDecl e -> do
     mt <- view (valEnv . at v)
     (xv, _ty) <- case mt of
       Nothing -> fail "internal error: ToF.valueDecl FunDecl did not find type declaration for field"
       Just xty -> return xty
     m <- expr e
     let mr = F.Record [(F.FVal, m)]
     declarations ds $ \ans -> do
       (a, mstruct) <- kont $ (mempty, [(F.FUser f, F.V xv)]) <> ans
       return (a, F.Let $ U.bind (xv, U.embed mr) $ mstruct)
   _ -> fail "unimplemented ToF.valueDecl"

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

expr :: ToF m => Expr -> m F.Term
expr _ = fail "unimplemented: ToF.expr"
