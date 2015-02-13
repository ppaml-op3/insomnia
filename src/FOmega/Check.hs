{-# LANGUAGE ViewPatterns, FlexibleContexts,
     FlexibleInstances,
     TypeSynonymInstances
  #-}
module FOmega.Check where

import Control.Monad.Reader
import Data.Monoid
import qualified Data.List as List
import qualified Data.Set as S
import Control.Monad.Except


import qualified Unbound.Generics.LocallyNameless as U
import Unbound.Generics.LocallyNameless.LFresh (LFresh, LFreshMT, runLFreshMT)

import FOmega.Syntax


data Ctx =
  CNil
  | CCons !CBind !Ctx

data CBind =
  CVal !Var !Type 
  | CType !TyVar !Kind

newtype Expected a = Expected { unExpected :: a }
                     deriving (Show)

newtype Got a = Got { unGot :: a }
              deriving (Show)

data OmegaErr =
  TypeAppArgKindMismatch !Type !(Expected Kind) !Type !(Got Kind)
  | TypeAppNotArr !Type !(Got Kind)
  | ExpectedKType !Type !(Got Kind)
  | UnboundTypeVariable !TyVar
  | UnboundVariable !Var
  | ApplicationNotAFun !Term !(Got Type)
  | PolyAppArgKindMismatch !Term !(Expected Kind) !Type !(Got Kind)
  | PolyAppNotAFun !Term !(Got Type)
  | UnexpectedType !(Expected Type) !(Got Type)
  | ExistentialKindMismatch !(Expected Kind) !(Got Type) !(Got Kind)
  | UnpackBodyMentionsVar !Type !TyVar !(Got Type)
  | UnpackNotExist !(Got Type)
  | ProjectFromNonRecord !(Got Type) !(Expected Field)
  | FieldNotFound !(Expected Field) !(Got [Field])
  | MalformedStylizedRecord !(Got [Field])
  | SampleBodyNotDist !(Got Type)
  | SampleFromNonDist !(Got Type)
  | AppendErr !OmegaErr !OmegaErr
  | NoErr
  deriving (Show)

instance Monoid OmegaErr where
  mempty = NoErr
  mappend NoErr m = m
  mappend m NoErr = m
  mappend (AppendErr m1 m2) m3 = mappend m1 (mappend m2 m3)
  mappend m1 m2 = AppendErr m1 m2

type TC m = ReaderT Ctx (ExceptT OmegaErr (LFreshMT m))

class (LFresh m, MonadReader Ctx m, MonadError OmegaErr m, MonadPlus m) => MonadTC m
instance Monad m => MonadTC (TC m)

runTC :: TC m a -> m (Either OmegaErr a)
runTC c = runLFreshMT $ runExceptT (runReaderT c CNil)

inferK :: MonadTC m => Type -> m Kind
inferK t_ =
  case t_ of
   TV v -> lookupTyVar v
   TLam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
       kbody <- extendEnv (CType v k) $ inferK tbody
       return $ KArr k kbody
   TApp tfn targ -> do
     kfn <- inferK tfn
     karg <- inferK targ
     case kfn of
      KArr karg' kres | karg == karg' -> return kres
                      | otherwise -> throwError (TypeAppArgKindMismatch tfn (Expected karg') targ (Got karg))
      KType -> throwError (TypeAppNotArr tfn (Got KType))
   TForall bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
       kbody <- extendEnv (CType v k) $ inferK tbody
       expectKType tbody kbody
       return KType
   TExist ep -> do
     checkExistPack ep
     return KType
   TArr t1 t2 -> do
     k1 <- inferK t1
     expectKType t1 k1
     k2 <- inferK t2
     expectKType t2 k2
     return KType
   TRecord fts -> do
     forM_ fts $ \(_f, t) -> do
       k <- inferK t
       expectKType t k
     ensureDistinctFields $ map fst fts
     wellFormedStylizedRecord fts
     return KType
   TDist t -> do
     k <- inferK t
     expectKType t k
     return KType

checkExistPack :: MonadTC m => ExistPack -> m ()
checkExistPack bnd =
  U.lunbind bnd $ \((v, U.unembed -> k), tbody) -> do
    kbody <- extendEnv (CType v k) $ inferK tbody
    expectKType tbody kbody

inferTy :: MonadTC m => Term -> m Type
inferTy m_ =
  case m_ of
   V v -> lookupVar v
   Lam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> t), body) -> do
       k <- inferK t
       expectKType t k
       -- TODO: normalize t here?
       t' <- extendEnv (CVal v t) $ inferTy body
       return $ TArr t t'
   App f m -> do
     tfn <- inferTy f
     targ <- inferTy m
     tfnN <- whnfTy tfn KType
     case tfnN of
      TArr targ' tres -> do
        _argNorm <- tyEquiv (Expected targ') (Got targ) KType
        return tres
      tother -> throwError $ ApplicationNotAFun f (Got tother)
   PLam bnd ->
     U.lunbind bnd $ \((v, U.unembed -> k), m) -> do
       tbody <- extendEnv (CType v k) $ inferTy m
       return $ TForall $ U.bind (v, U.embed k) tbody
   PApp m a -> do
     tfn <- inferTy m
     karg <- inferK a
     tfnN <- whnfTy tfn KType
     case tfnN of
      TForall bnd ->
        U.lunbind bnd $ \((tv, U.unembed -> karg'), tres) -> do
          unless (karg == karg') $
            throwError $ PolyAppArgKindMismatch m (Expected karg') a (Got karg)
          return $ U.subst tv a tres
      tother -> throwError $ PolyAppNotAFun m (Got tother)
   Pack a m ep -> do
     k <- inferK a
     t <- inferTy m
     checkExistPack ep
     t' <- instExistPack a k ep
     _bodyNorm <- tyEquiv (Expected t) (Got t') KType
     return $ TExist ep
   Unpack bnd ->
     U.lunbind bnd $ \((tv, xv, U.unembed -> m), mbody) -> do
       t <- inferTy m
       tN <- whnfTy t KType
       case tN of
        TExist ep ->
          U.lunbind ep $ \((tv', U.unembed -> k), tx_) -> do
            let tx = U.subst tv' (TV tv) tx_
            tbody <- extendEnv (CType tv k) $ extendEnv (CVal xv tx) $ inferTy mbody
            (inferK tbody >>= expectKType tbody)
              `mplus` (throwError $ UnpackBodyMentionsVar tbody tv (Got tN))
            return tbody
        _ -> throwError $ UnpackNotExist (Got tN)
   Record fms -> do
     fts <- forM fms $ \(f, m) -> do
       t <- inferTy m
       return (f, t)
     ensureDistinctFields $ map fst fms
     wellFormedStylizedRecord fts
     return $ TRecord fts
   Proj m f -> do
     t <- inferTy m
     tN  <- whnfTy t KType
     case tN of
      TRecord fts ->
        lookupField fts f
      _ -> throwError $ ProjectFromNonRecord (Got t) (Expected f)
   Let bnd ->
     U.lunbind bnd $ \((x, U.unembed -> m1), m2) -> do
       t <- inferTy m1
       extendEnv (CVal x t) $ inferTy m2
   Return m -> do
     t <- inferTy m
     return $ TDist t
   LetSample bnd ->
     U.lunbind bnd $ \((x, U.unembed -> m1), m2) -> do
       t <- inferTy m1
       case t of
        TDist t' -> do
          t'' <- extendEnv (CVal x t') $ inferTy m2
          case t'' of
           TDist {} -> return t''
           _ -> throwError $ SampleBodyNotDist (Got t'')
        _ -> throwError $ SampleFromNonDist (Got t)
   
instExistPack :: MonadTC m => Type -> Kind -> ExistPack -> m Type
instExistPack t k bnd =
  U.lunbind bnd $ \((v, U.unembed -> k'), tbody) -> do
    unless (k == k') $
      throwError $ ExistentialKindMismatch (Expected k') (Got t) (Got k)
    return $ U.subst v t tbody

------------------------------------------------------------
-- * Type normalization and equivalence

whnfTy :: MonadTC m => Type -> Kind -> m Type
whnfTy t k_ =
  case t of
   TApp t1 t2 -> do
     k2 <- inferK t2
     t1N <- whnfTy t1 (k2 `KArr` k_)
     case t1N of
      TLam bnd ->
        U.lunbind bnd $ \((v, _), tbody) ->
        whnfTy (U.subst v t2 tbody) KType
      _ -> return $ TApp t1N t2
   TLam bnd ->
     U.lunbind bnd $ \(vk@(v, _), tbody) ->
     case k_ of
      (KArr k1 k2) -> do
        tbodyN <- extendEnv (CType v k1) $ whnfTy tbody k2
        return $ TLam $ U.bind vk tbodyN
      KType -> fail "impossible for well-kinded terms"
   _ -> return t

tyEquiv :: MonadTC m => Expected Type -> Got Type -> Kind -> m Type
tyEquiv e@(Expected t1) g@(Got t2) k =
  tyEquiv' t1 t2 k `mplus` throwError (UnexpectedType e g)

tyEquiv' :: MonadTC m => Type -> Type -> Kind -> m Type
tyEquiv' t1_ t2_ k = do
  t1N_ <- whnfTy t1_ k
  t2N_ <- whnfTy t2_ k
  case (t1N_, t2N_, k) of
   (TV {}, TV {}, _) -> do
     (tA, _k) <- tyAtEquiv t1N_ t2N_
     return tA
   (TApp {}, TApp {}, _) -> do
     (tA, _k) <- tyAtEquiv t1N_ t2N_
     return tA
   (TArr s1 t1, TArr s2 t2, KType) -> do
     sN <- tyEquiv' s1 s2 KType
     tN <- tyEquiv' t1 t2 KType
     return $ TArr sN tN
   (TForall bnd1, TForall bnd2, KType) -> do
     U.lunbind2 bnd1 bnd2 $ \m ->
       case m of
        Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
          guard (k1 == k2)
          tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 KType
          return $ TForall $ U.bind p tN
        Nothing -> mzero
   (TExist bnd1, TExist bnd2, KType) -> do
     U.lunbind2 bnd1 bnd2 $ \m ->
       case m of
        Just (p@(v, U.unembed -> k1), t1, (_, U.unembed -> k2), t2) -> do
          guard (k1 == k2)
          tN <- extendEnv (CType v k1) $ tyEquiv' t1 t2 KType
          return $ TExist $ U.bind p tN
        Nothing -> mzero
   (TRecord fts, TRecord gts, KType) -> do
     let allFieldNames = S.toList $ mconcat $ map (S.fromList . map fst) [fts, gts]
     ftsN <- forM allFieldNames $ \f -> do
       t1 <- lookupField fts f
       t2 <- lookupField gts f
       tN <- tyEquiv' t1 t2 KType
       return (f, tN)
     return $ TRecord ftsN
   (_, _, KArr k1 k2) -> do
     v <- U.lfresh (U.s2n "a")
     let
       tv = TV v
       t1 = TApp t1_ tv
       t2 = TApp t2_ tv
     t1N <- extendEnv (CType v k1) $ tyEquiv' t1 t2 k2
     return $ TLam $ U.bind (v, U.embed k1) t1N
   (_, _, KType) -> mzero -- not equivalent
     
-- | Compare types in atomic form for equivalence.  An atomic type has
-- a variable at the head of a sequence of application.
tyAtEquiv :: MonadTC m => Type -> Type -> m (Type, Kind)
tyAtEquiv t1_ t2_ =
  case (t1_, t2_) of
   (TV v1, TV v2) ->
     if v1 == v2
     then do
       k <- lookupTyVar v1
       return (t1_, k)
     else mzero
   (TApp t1A s1, TApp t2A s2) -> do
     (tA, kt) <- tyAtEquiv t1A t2A
     case kt of
      KType -> mzero
      KArr ks k -> do
        sN <- tyEquiv' s1 s2 ks
        return (TApp tA sN, k)
   (_, _) -> mzero
     
------------------------------------------------------------
-- * Utilities

ensureDistinctFields :: MonadTC m => [Field] -> m ()
ensureDistinctFields _ = return () -- TODO: actually ensure

-- | Records that contain builtin-fields have a certain expected form:
-- 1. If a FVal, FType or FSig field is present, it is the only field.
-- 2. If a FData field is present, there may be zero or more FCon fields and no others.
-- 3. Otherwise all fields must be FUser
wellFormedStylizedRecord :: MonadTC m => [(Field, a)] -> m ()
wellFormedStylizedRecord [(FVal, _)] = return ()
wellFormedStylizedRecord [(FType, _)] = return ()
wellFormedStylizedRecord [(FSig, _)] = return ()
wellFormedStylizedRecord fs = do
  let userRecord = all isUser fs
      isDatatype =
        case List.partition isData fs of
         ([_d], cs) -> all isCon cs
         _ -> False
  unless (userRecord || isDatatype) $
    throwError $ MalformedStylizedRecord (Got $ map fst fs)
  where
    isUser (FUser {}, _) = True
    isUser _ = False
    isData (FData, _) = True
    isData _ = False
    isCon (FCon {}, _) = True
    isCon _ = False

lookupField :: MonadTC m => [(Field, a)] -> Field -> m a
lookupField fs_ f = go fs_
  where
    go [] = throwError $ FieldNotFound (Expected f) (Got $ map fst fs_)
    go ((f',x):fs) | f == f' = return x
                   | otherwise = go fs

extendEnv :: MonadTC m => CBind -> m a -> m a
extendEnv b = local (CCons b)

expectKType :: MonadTC m => Type -> Kind -> m ()
expectKType t k =
  case k of
   KType -> return ()
   KArr {} -> throwError $ ExpectedKType t (Got k)

lookupTyVar :: MonadTC m => TyVar -> m Kind
lookupTyVar v = do
  m <- asks (findTyVar v)
  case m of
   Nothing -> throwError $ UnboundTypeVariable v
   Just k -> return k

lookupVar :: MonadTC m => Var -> m Type
lookupVar v = do
  m <- asks (findVar v)
  case m of
   Nothing -> throwError $ UnboundVariable v
   Just t -> return t

findTyVar :: TyVar -> Ctx -> Maybe Kind
findTyVar v = go
  where
    go CNil = Nothing
    go (CCons b c) =
      case b of
      CType v' k | v == v' -> Just k
      _ -> go c

findVar :: Var -> Ctx -> Maybe Type
findVar v = go
  where
    go CNil = Nothing
    go (CCons b c) =
      case b of
       CVal v' t | v == v' -> Just t
       _ -> go c

