{-# LANGUAGE OverloadedStrings #-}
-- | Kind checking for types.
-- Well-formed kind checking is also here because it is trivial.
module Insomnia.Typecheck.Type where

import Control.Lens
import Control.Monad (zipWithM_, forM)
import Control.Monad.Reader.Class (MonadReader(..))

import Data.List (intersperse)
import Data.Monoid (Monoid(..),(<>))
import qualified Data.Set as S

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.TypeDefn (TypeAlias(..))
import Insomnia.Types

import Insomnia.Typecheck.Env

-- | Check that a kind is well-formed.  Note that for now, all kinds
-- are well-formed.
checkKind :: Kind -> TC ()
checkKind _k = return ()

-- | The subkinding relation. For our simple kinds it is reflexive.
isSubkind :: Kind -> Kind -> Bool
isSubkind = U.aeq

-- | ensure that the first kind is a subtype of the second.
ensureSubkind :: (Type, Kind) -> Kind -> TC ()
ensureSubkind (tblame, ksub) ksup =
  if (isSubkind ksub ksup)
  then return ()
  else typeError (formatErr tblame
                  <> " has kind "
                  <> formatErr ksub
                  <> " which is not a subkind of "
                  <> formatErr ksup)

-- | Ensure that the given kind is of the form (k1 → k2).
ensureKArr :: Kind -> Type -> TC (Kind, Kind)
ensureKArr k t =
  case k of
    KType -> typeError ("expected an arrow kind, got ⋆ when checking "
                        <> formatErr t)
    KArr k1 k2 -> return (k1, k2)

-- | Check that a type has the given kind
checkType :: Type -> Kind -> TC Type
checkType t k = do
  tk@(t', _) <- inferType t
  ensureSubkind tk k
  return t'

-- | Given a type, infer its kind.
inferType :: Type  -> TC (Type, Kind)
inferType t =
  case t of
    TC {} ->
      expandAliasApplication t []
    TApp t1 t2 ->
      expandAliasApplication t1 [t2]
    TUVar u -> typeError ("unexpected unification variable "
                          <> formatErr u)
    TV v -> do
      k' <- lookupTyVar v
      return (t, k')
    TAnn t1 k1 -> do
      checkKind k1
      t1' <- checkType t1 k1
      return (TAnn t1' k1, k1)
    TForall bnd -> do
      U.lunbind bnd $ \((v, kdom), tcod) -> do
        checkKind kdom
        tcod' <- extendTyVarCtx v kdom $ checkType tcod KType
        return (TForall (U.bind (v, kdom) tcod'), KType)        
    TRecord row -> do
      row' <- checkRow row
      return (TRecord row', KType)

checkRow :: Row -> TC Row
checkRow r@(Row ts) = do
  checkUniqueLabels r
  ts' <- forM ts $ \(lbl, ty) -> do
    ty' <- checkType ty KType
    return (lbl, ty')
  return $ Row $ canonicalOrderRowLabels ts'

checkUniqueLabels :: Row -> TC ()
checkUniqueLabels r@(Row ls0) =
  case dups S.empty ls0 of
   Just l ->  typeError ("duplicate label " <> formatErr l
                         <> " in row type " <> formatErr r)
   Nothing -> return ()
  where
    dups _seen [] = Nothing
    dups seen ((l,_ty):ls) =
      if l `S.member` seen
      then Just l
      else dups (S.insert l seen) ls

-- | @expandAliasApplication t targs@ recursively unfolds t until a
-- type alias is exposed which is then expanded with the given
-- arguments and the resulting type is returned.  If the head is some
-- other higher-kinded type, the sequence of type applications is
-- typechecked in the normal manner and the result type is just the
-- sequence of type applcations.
--
-- Notes:
-- 1. It is an error to apply a type alias to fewer arguments than it expects.
-- 2. The result of expanding a type alias may be higher-kinded, so the alias
--    could appear under _more_ applications than its number of arguments.
-- 3. The result of expanding an alias may itself be an alias.  Cycles are
--    assumed not to occur, so we expand recursively until there are no more
--    aliases at the head.
expandAliasApplication :: Type -> [Type] -> TC (Type, Kind)
expandAliasApplication t targs =
  case t of
    TApp t' targ -> expandAliasApplication t' (targ:targs)
    TC dcon -> do
      desc <- lookupDCon dcon
      case desc of
        GenerativeTyCon gt -> do
          k' <- inferGenerativeType gt
          reconstructApplication (t,k') targs
        AliasTyCon aliasInfo aliasClosure -> do
          m <- checkAliasInfoArgs aliasInfo targs
          case m of
           Left (_wantMoreArgs, kt) -> reconstructApplication (t, kt) targs
           Right (tsubArgs, tAppArgs) -> do
             tRHS <- expandAliasClosure aliasClosure tsubArgs
             -- maybe RHS is also an alias, expand it again.
             expandAliasApplication tRHS tAppArgs
    TV v -> do
      k' <- lookupTyVar v
      reconstructApplication (t, k') targs
    _ ->
      case targs of
       [] -> inferType t
       _ -> typeError ("Type " <> formatErr t
                       <> " cannot be applied to "
                       <> mconcat (intersperse ", " $ map formatErr targs))

type RequiredArgsCount = Int

-- | Given a type alias and some number of types to which it is applied,
-- split up the arguments into the set that's required by the alias,
-- and the rest to which the RHS of the alias will be applied.
-- Also check that the mandatory args are of the correct kind.
checkAliasInfoArgs :: TypeAliasInfo -> [Type] -> TC (Either (RequiredArgsCount, Kind)
                                                                        ([Type], [Type]))
checkAliasInfoArgs (TypeAliasInfo kargs kRHS) targs = do
  let
    n = length kargs
  if (length targs < n)
    then return $ Left (n, kargs `kArrs` kRHS)
    else let (tsubArgs, tAppArgs) = splitAt n targs
         in do
           zipWithM_ checkType tsubArgs kargs
           return $ Right (tsubArgs, tAppArgs)

expandAliasClosure :: TypeAliasClosure -> [Type] -> TC Type
expandAliasClosure (TypeAliasClosure env (ManifestTypeAlias bnd)) targs =
  local (const env)
  $ U.lunbind bnd
  $ \(tvks, ty) -> return $ let tvs = map fst tvks
                                substitution = zip tvs targs
                            in U.substs substitution ty
expandAliasClosure (TypeAliasClosure _env (DataCopyTypeAlias tp _defn)) targs =
  return $ (TC $ TCGlobal tp) `tApps` targs

-- | @reconstructApplication (thead, khead) [t1,...,tN]@ returns the
-- type @thead `TApp` t1 `TApp` ... `TApp` tN@ and its infered kind
-- after checking that each argument checks against its corresponding
-- kind in @khead@
reconstructApplication :: (Type, Kind) -> [Type] -> TC (Type, Kind)
reconstructApplication (thead, k) targs =
  case targs of
    [] -> return (thead, k)
    (targ:targs') -> do
      (kdom, kcod) <- ensureKArr k thead
      targ' <- checkType targ kdom
      reconstructApplication (TApp thead targ', kcod) targs'

inferGenerativeType :: GenerativeType -> TC Kind
inferGenerativeType (AlgebraicType algTy) =
  let k = foldr KArr KType (algTy^.algTypeParams)
  in return k
inferGenerativeType (EnumerationType {}) = return KType
inferGenerativeType (AbstractType k) = return k
  

