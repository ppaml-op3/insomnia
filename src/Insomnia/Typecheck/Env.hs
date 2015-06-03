{-# LANGUAGE TemplateHaskell, OverloadedStrings,
      FlexibleContexts, FlexibleInstances, MultiParamTypeClasses
  #-}
-- | The typechecking environment.
--
-- This module defines the typing context and the
-- typechecking monad.
module Insomnia.Typecheck.Env where

import Control.Lens

import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.Trans.Reader (ReaderT (..))
import Control.Monad.Error.Class (MonadError(..))

import Data.Format (Format(..))
import qualified Data.Format as F
import qualified Data.Map as M
import Data.Monoid (Monoid(..), (<>))

import qualified Unbound.Generics.LocallyNameless as U
import Unbound.Generics.LocallyNameless.LFresh (LFreshMT, runLFreshMT)

import Control.Monad.Except (Except, runExcept)

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.TypeDefn (TypeAlias(..),
                          ValConName, ValConPath(..),
                          InferredValConPath(..),
                          ValueConstructor(..))
import Insomnia.Expr (Var, QVar)
import Insomnia.ModuleType (ToplevelSummary, ModuleTypeNF(..))

import Insomnia.Unify (MonadUnificationExcept(..),
                       UVar,
                       UnificationT,
                       runUnificationT)

import Insomnia.Pretty (Pretty(..), ppDefault, ppTypeAlias,
                        text, vcat, fsep, punctuate)


-- | Type checker errors
newtype TCError = TCError { getTCError :: F.Doc }

instance Format TCError where
  format = format . getTCError

type ConstructorArgs = (U.Bind [KindedTVar] [Type])

-- each constructor C of algebraic datatype D has the form:
--  ∀ (α₁ ∷ K₁, … αᵢ ∷ Kᵢ) . T₁ → T₂ → ⋯ → D α₁ ⋯ αᵢ
-- (if we add GADTs, there will also be existential β vars and
-- equality constraints.  In any case, D will always be applied to exactly
-- the αs and we don't bother storing the whole application.  Just the head
-- data constructor D.)
data AlgConstructor =
  AlgConstructor {
    _algConstructorArgs :: ConstructorArgs
    , _algConstructorDCon :: TypeConstructor
    }
  deriving (Show)
           
data AlgType =
  AlgType {
    _algTypeParams :: [Kind] -- ^ the ADT is parametric, having kind κ1→⋯→κN→⋆
    , _algTypeCons :: [ValueConstructor] -- ^ the names of the constructors in this kind.
    }

-- | Types that arise as a result of checking a declaration.  Each
-- declaration gives rise to a new type that is distinct even from
-- other declarations that appear structurally equivalent.  (Formally
-- these may be modeled by singleton kinds or by definitions in a
-- typing context.)
data GenerativeType =
  AlgebraicType !AlgType -- ^ an (AlgebraicType κs) declares a type of kind κ1 → ⋯ → κN → ⋆
  | EnumerationType !Nat -- ^ a finite enumeration type of N elements
  | AbstractType !Kind -- ^ an abstract type with no (visible) definition.
--   | RecordType Rows -- ^ a record type with the given rows

data TypeAliasInfo =
  TypeAliasInfo { _typeAliasInfoMandatoryArity :: [Kind] -- type parameters that the type alias requires
                , _typeAliasInfoRHSKind :: Kind -- the kind of the result of the alias
                }

-- | Type constructor descriptors.  A type constructor is either
-- generative (denotes a "new" type) or it is an alias.
data TyConDesc =
  GenerativeTyCon !GenerativeType
  | AliasTyCon !TypeAliasInfo !TypeAliasClosure

-- | A Type alias closure captures the environment (actually just the tycon descriptors, due to phase distinction)
data TypeAliasClosure = TypeAliasClosure !Env !TypeAlias

data ValueConstructorIdx =
  VCILocal !ValConName
  | VCIGlobal !ValConPath
    deriving (Show, Eq, Ord)

-- | Typechecking environment
data Env = Env {
  -- | toplevel references
  _envTopSums :: M.Map TopRef ToplevelSummary
  -- | signatures
  , _envSigs :: M.Map SigIdentifier ModuleTypeNF
    -- | modules' unselfified signatures (invariant: their selfified
    -- contents have been added to DCons and Globals iff their are a SigMTNF (SigV _ ModuleK)
  , _envModuleSigs :: M.Map Identifier ModuleTypeNF
    -- | type constructor descriptors
  , _envDCons :: M.Map TypeConstructor TyConDesc
    -- | value constructors
  , _envCCons :: M.Map ValueConstructorIdx AlgConstructor
    -- | declared global vars
  , _envGlobals :: M.Map QVar Type
    -- | defined vars in the current module
  , _envGlobalDefns :: M.Map Var ()
    -- | local type variables
  , _envTys :: M.Map TyVar Kind
    -- | local value variables
  , _envLocals :: M.Map Var Type
    -- | local vars that may be used as indices of tabulated
    -- functions.  (Come into scope in "forall" expressions)
  , _envVisibleSelector :: M.Map Var ()
  }


$(makeLenses ''AlgConstructor)
$(makeLenses ''AlgType)
$(makeLenses ''TypeAliasInfo)

$(makeLenses ''Env)

instance Pretty AlgConstructor where
  pp = text . show

instance Pretty ValueConstructorIdx where
  pp (VCILocal n) = pp n
  pp (VCIGlobal p ) = pp p
  

instance Pretty AlgType where
  pp alg = vcat ["params"
                , fsep $ punctuate "," (map pp (alg^.algTypeParams))
                , "constructors"
                , fsep $ punctuate "|" (map pp (alg^.algTypeCons))
                ]

instance Pretty GenerativeType where
  pp (AlgebraicType alg) = pp alg
  pp (EnumerationType n) = pp n
  pp (AbstractType k) = pp k

instance Pretty TyConDesc where
  pp (GenerativeTyCon gt) = pp gt
  pp (AliasTyCon _ clo) = pp clo

instance Pretty TypeAliasClosure where
  pp (TypeAliasClosure _ a) = ppTypeAlias "_" a


instance Pretty Env where
  pp env = vcat [ "toplevels", pp (env^.envTopSums)
                , "sigs", pp (env^.envSigs)
                , "modules", pp (env^.envModuleSigs)
                , "dcons", pp (env^.envDCons)
                , "ccons", pp (env^.envCCons)
                , "globals", pp (env^.envGlobals)
                , "locals", pp (env^.envLocals)
                , "defnitions", pp (env^.envGlobalDefns)
                                  -- TODO: the rest of the env
                ]

typeAliasInfoKind :: TypeAliasInfo -> Kind
typeAliasInfoKind (TypeAliasInfo kdoms kcod) = kArrs kdoms kcod

-- | The empty typechecking environment
emptyEnv :: Env
emptyEnv = Env mempty mempty mempty mempty mempty mempty mempty mempty mempty mempty

-- | Base environment with builtin types.
baseEnv :: Env
baseEnv = emptyEnv
          & (envDCons . at conArrow) ?~ GenerativeTyCon (AlgebraicType algArrow)
          & (envDCons . at conDist) ?~ GenerativeTyCon (AlgebraicType algDist)
          & (envDCons . at conInt) ?~ GenerativeTyCon (AlgebraicType algInt)
          & (envDCons . at conReal) ?~ GenerativeTyCon (AlgebraicType algReal)

builtinCon :: String -> TypeConstructor
builtinCon = TCLocal . U.s2n

-- | Base data constructors
conArrow :: TypeConstructor
conArrow = builtinCon "->"

conDist :: TypeConstructor
conDist = builtinCon "Dist"

conInt :: TypeConstructor
conInt = builtinCon "Int"

conReal :: TypeConstructor
conReal = builtinCon "Real"

algArrow :: AlgType
algArrow = AlgType [KType, KType] []

algDist :: AlgType
algDist = AlgType [KType] []

algInt :: AlgType
algInt = AlgType [] []

algReal :: AlgType
algReal = AlgType [] []

functionT :: Type -> Type -> Type
functionT t1 t2 = TC conArrow `TApp` t1 `TApp` t2

functionT' :: [Type] -> Type -> Type
functionT' [] = id
functionT' (tdom:tdoms) = functionT tdom . functionT' tdoms

distT :: Type -> Type
distT tsample = TC conDist `TApp` tsample

intT :: Type
intT = TC conInt

realT :: Type
realT = TC conReal


-- | The typechecking monad sans unification
type TCSimple = ReaderT Env (LFreshMT (Except TCError))

-- | The typechecking monad
type TC = UnificationT Kind Type TCSimple

-- instance MonadUnificationExcept Type TCSimple
instance MonadUnificationExcept TypeUnificationError Kind Type (ReaderT Env (LFreshMT (Except TCError))) where
  throwUnificationFailure err = do
    env <- ask
    throwError $ TCError (formatErr err
                          <> "\nEnvironment:\n"
                          <> formatErr env)

-- | Run a typechecking computation
runTC :: TC a -> Either TCError (a, M.Map (UVar Kind Type) Type)
runTC comp =
  runExcept $ runLFreshMT $ runReaderT (runUnificationT comp) baseEnv

-- instance MonadTypeAlias TC
instance MonadTypeAlias (UnificationT Kind Type TCSimple) where
  expandTypeAlias c = do
    md <- view (envDCons . at c)
    case md of
     Just (AliasTyCon _ (TypeAliasClosure _env (ManifestTypeAlias bnd))) ->
           U.lunbind bnd $ \(tvks, ty) ->
           case tvks of
            [] -> return (Just ty)
            _ -> unimplemented "Env.expandTypeAlias for aliases with arguments"
     Just (AliasTyCon _ (TypeAliasClosure _env (DataCopyTypeAlias tp _))) ->
       return $ Just $ TC $ TCGlobal tp
     _ -> return Nothing

-- | Given a value constructor c, return its type as a polymorphic function
--   (that is, ∀ αs . T1(αs) → ⋯ → TN(αs) → D αs)
mkConstructorType :: AlgConstructor -> TC Type
mkConstructorType constr = 
  -- XX could do unsafeBunbind here for working under the binder.
  U.lunbind (constr^.algConstructorArgs) $ \ (tvks, targs) -> do
  let tvs = map (TV . fst) tvks
      d = constr^.algConstructorDCon
      -- data type applied to the type variables - D α1 ⋯ αK
      dt = tApps (TC d) tvs
      -- arg1 → (arg2 → ⋯ (argN → D αs))
      ty = functionT' targs dt
  -- ∀ αs . …
  return $ tForalls tvks ty

-- | Lookup info about a toplevel reference
lookupToplevelSummary :: TopRef -> TC ToplevelSummary
lookupToplevelSummary tr = do
  m <- view (envTopSums . at tr)
  case m of
   Just tsum -> return tsum
   Nothing -> typeError $ "no toplevel reference " <> formatErr tr

-- | Lookup info about a (toplevel) module.
lookupModuleSig :: Identifier -> TC ModuleTypeNF
lookupModuleSig ident = do
  m <- view (envModuleSigs . at ident)
  case m of
    Just sigv -> return sigv
    Nothing -> typeError $ "no module " <> formatErr ident

-- | Look up info about a datatype
lookupDCon :: TypeConstructor -> TC TyConDesc
lookupDCon d = do
  m <- view (envDCons . at d)
  case m of
    Just k -> return k
    Nothing -> typeError $ "no data type " <> formatErr d

lookupValueConstructor :: ValueConstructor -> TC (ValueConstructor, AlgConstructor)
lookupValueConstructor vc = do
  let
    vci = case vc of
      VCLocal i -> VCILocal i
      VCGlobal (Left p) -> VCIGlobal p
  m <- view (envCCons . at vci)
  case m of
    Just constr -> do
      let vc' = a2vc constr
      return (vc', constr)
    Nothing -> typeError $ "no datatype defines a constructor " <> formatErr vc
  where
    a2vc c =
      case vc of
      VCLocal {} -> vc
      VCGlobal (Left (ValConPath _ f)) ->
        VCGlobal (Right (InferredValConPath
                         (c^.algConstructorDCon.to toTypePath)
                         f))
    toTypePath (TCGlobal p) = p
    toTypePath (TCLocal _) =
      error "internal error: local type constructor for global value constructor"

-- | Lookup the kind of a type variable
lookupTyVar :: TyVar -> TC Kind
lookupTyVar tv = do
  m <- view (envTys . at tv)
  case m of
    Just k -> return k
    Nothing -> typeError $ "no type variable " <> formatErr tv

lookupGlobal :: QVar -> TC (Maybe Type)
lookupGlobal v = view (envGlobals . at v)

lookupLocal :: Var -> TC (Maybe Type)
lookupLocal v = view (envLocals . at v)

-- | Checks tht the given identifier is bound in the context to a
-- signature.
lookupModuleType :: SigIdentifier -> TC ModuleTypeNF
lookupModuleType ident = do
  mmsig <- view (envSigs . at ident)
  case mmsig of
    Just sigv -> return sigv
    Nothing -> typeError ("no model type " <> formatErr ident
                          <> " in scope")

extendToplevelSummaryCtx :: MonadReader Env m
                            => TopRef -> ToplevelSummary -> m a -> m a
extendToplevelSummaryCtx tr tsum = local (envTopSums . at tr ?~ tsum)

-- | Extend the toplevel modules environment by adding the given
-- module.  Invariant - the selfified types, constructors and terms
-- should be added separately using extendDConCtx, etc.
extendModuleSigCtx :: MonadReader Env m
                      => Identifier -> ModuleTypeNF -> m a -> m a
extendModuleSigCtx ident sigv =
  local (envModuleSigs . at ident ?~ sigv)

-- | Extend the type signatures environment by adding the given
-- signature.
extendModuleTypeCtx :: MonadReader Env m
                       => SigIdentifier -> ModuleTypeNF -> m a -> m a
extendModuleTypeCtx ident sigv =
  local (envSigs . at ident ?~ sigv)


-- | Extend the data type environment by adding the declaration
-- of the given data type with the given kind
extendDConCtx :: MonadReader Env m => TypeConstructor -> TyConDesc -> m a -> m a
extendDConCtx dcon k = local (envDCons . at dcon ?~ k)

extendConstructorsCtx :: MonadReader Env m => [(ValueConstructor, AlgConstructor)] -> m a -> m a
extendConstructorsCtx cconstrs =
  local (envCCons %~ M.union (M.fromList $ map (\(vc, a) -> (vc2i vc, a)) cconstrs))
  where
    vc2i (VCLocal vc) = VCILocal vc
    vc2i (VCGlobal (Left p)) = VCIGlobal p
    vc2i (VCGlobal (Right (InferredValConPath (TypePath p _) f))) = VCIGlobal (ValConPath p f)

extendValueDefinitionCtx :: Var -> TC a -> TC a
extendValueDefinitionCtx v =
  local (envGlobalDefns %~ M.insert v ())

-- | @extendTyVarCtx a k comp@ Extend the type environment of @comp@
-- with @a@ having the kind @k@.
extendTyVarCtx :: TyVar -> Kind -> TC a -> TC a
extendTyVarCtx a k =
  -- no need for U.avoid since we used U.lunbind when we brough the
  -- variable into scope.
  local (envTys . at a ?~ k)

-- | Extend the type environment with all the given type variables
-- with the given kinds.  Assumes the variables are distinct.
-- Does not add to the avoid set because we must have already called U.lunbind.
extendTyVarsCtx :: [(TyVar, Kind)] -> TC a -> TC a
extendTyVarsCtx vks = local (envTys %~ M.union (M.fromList vks))

-- | Extend the local variables environment by adding the given
-- variable (assumed to be free and fresh) with the given type (which may be
-- a UVar)
extendLocalCtx :: Var -> Type -> TC a -> TC a
extendLocalCtx v t = local (envLocals . at v ?~ t)

extendLocalsCtx :: [(Var, Type)] -> TC a -> TC a
extendLocalsCtx vts = local (envLocals %~ M.union (M.fromList vts))

-- | Make the given vars be the only legal selectors when runnning
-- the given computation
settingVisibleSelectors :: [Var] -> TC a -> TC a
settingVisibleSelectors vs =
  local (envVisibleSelector .~ vsMap)
  where
    vsMap = M.fromList (map (\k -> (k, ())) vs)

guardDuplicateDConDecl :: TypeConstructor -> TC ()
guardDuplicateDConDecl dcon = do
  mdata <- view (envDCons . at dcon)
  case mdata of
    Nothing -> return ()
    Just _ -> typeError ("data type "
                         <> formatErr dcon
                         <> " is already defined")

guardDuplicateCConDecl :: ValueConstructor -> TC ()
guardDuplicateCConDecl ccon = do
  let vci = case ccon of
        VCLocal i -> VCILocal i
        VCGlobal (Left p) -> VCIGlobal p
  mcon <- view (envCCons . at vci)
  case mcon of
    Nothing -> return ()
    Just _ -> typeError ("value constructor "
                         <> formatErr ccon
                         <> " is already defined")
  where

ensureNoDefn :: Var -> TC ()
ensureNoDefn v = do
  m <- view (envGlobalDefns . at v)
  case m of
    Just () -> typeError ("duplicate defintion of " <> formatErr v)
    Nothing -> return ()


-- | Format some thing for error reporting.
formatErr :: (Pretty a) => a -> F.Doc
formatErr = format . ppDefault

-- | Throw some kind of type checking error
throwTCError :: TCError -> TC a
throwTCError = throwError

-- | Throw a type error with the given message.
typeError :: F.Doc -> TC a
typeError msg = do
  env <- ask
  throwTCError $ TCError ("type error: " <> msg
                          <> "\nEnvironment:\n"
                          <> formatErr env)

-- | Add an annotation to the type error from the given subcomputation
-- if it fails.
(<??@) :: TC a -> F.Doc -> TC a
comp <??@ note =
  catchError comp (\(TCError msg) -> throwTCError $ TCError (msg <> "\n"
                                                             <> note))

-- | A version of '<??@' with the arguments reversed.
(@??>) :: F.Doc -> TC a -> TC a
(@??>) = flip (<??@)

(.??@) :: (a -> TC b) -> F.Doc -> a -> TC b
(.??@) f note x =
  f x <??@ note

infixl 0 <??@
infixr 0 @??>


-- | Throw an error with the given message indicating that
-- part of the typechecker is unimplemented.
unimplemented :: F.Doc -> TC a
unimplemented msg =
  throwTCError . TCError $ "typecheck unimplemented: " <> msg
