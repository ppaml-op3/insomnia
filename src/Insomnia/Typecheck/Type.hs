{-# LANGUAGE OverloadedStrings #-}
-- | Kind checking for types.
-- Well-formed kind checking is also here because it is trivial.
module Insomnia.Typecheck.Type where

import Control.Lens
import Data.Monoid ((<>))

import qualified Unbound.Generics.LocallyNameless as U

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
    KType -> typeError ("expected an arrow kind, got ⋆ when checking"
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
    TC dcon -> do
      gt <- lookupDCon dcon
      k' <- inferGenerativeType gt
      return (t,k')
    TUVar u -> typeError ("unexpected unification variable "
                          <> formatErr u)
    TV v -> do
      k' <- lookupTyVar v
      return (t, k')
    TAnn t1 k1 -> do
      checkKind k1
      t1' <- checkType t1 k1
      return (TAnn t1' k1, k1)
    TApp t1 t2 -> do
      (t1', k1) <- inferType t1
      (k1dom, k1cod) <- ensureKArr k1 t
      t2' <- checkType t2 k1dom
      return (TApp t1' t2', k1cod)
    TForall bnd -> do
      U.lunbind bnd $ \((v, kdom), tcod) -> do
        checkKind kdom
        tcod' <- extendTyVarCtx v kdom $ checkType tcod KType
        return (TForall (U.bind (v, kdom) tcod'), KType)        

inferGenerativeType :: GenerativeType -> TC Kind
inferGenerativeType (AlgebraicType algTy) =
  let k = foldr KArr KType (algTy^.algTypeParams)
  in return k
inferGenerativeType (EnumerationType {}) = return KType
inferGenerativeType (AbstractType k) = return k
  

