{-# LANGUAGE OverloadedStrings,
             ViewPatterns
  #-}
module Insomnia.Typecheck ( Insomnia.Typecheck.Env.runTC
                          , checkToplevel
                          ) where

import Control.Lens
import Control.Applicative ((<$>))
import Control.Monad.Reader.Class (MonadReader(..))
import Data.Monoid (Monoid(..), (<>))

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr
import Insomnia.ModelType
import Insomnia.Toplevel

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ModelType (checkModelType, extendTypeSigDeclCtx)
import Insomnia.Typecheck.Selfify (selfifyTypeDefn)
import Insomnia.Typecheck.Model (inferModelExpr)

-- | Find a model type component with the given name in the context,
-- return its kind.
lookupPathType :: Path -> TC Kind
lookupPathType (IdP identifier) =
  typeError ("found module name "
             <> formatErr identifier
             <> ", but expected a type")
lookupPathType path_@(ProjP path field) = do
  s <- lookupModel path
  tdecl <- projectModelTypeTypeDecl s field
  k <- case tdecl ^. typeSigDeclKind of
    Nothing -> typeError ("internal error, path " <> formatErr path_
                          <> " has no kind associated in model type "
                          <> formatErr s)
    Just k -> return k
  return $ k

-- | Find a model with the given name in the context, return its
-- type.
lookupModel :: Path -> TC ModelType
lookupModel (IdP identifier) =
  unimplemented $ "lookupModel with identifier " <> formatErr identifier
lookupModel (ProjP model field) = do
  s <- lookupModel model
  projectModelTypeModel s field


projectModelTypeTypeDecl :: ModelType -> Field -> TC TypeSigDecl
projectModelTypeTypeDecl modelType field =
  unimplemented ("projectModelTypeTypeDecl " <> formatErr modelType
                 <> " field " <> formatErr field)

projectModelTypeModel :: ModelType -> Field -> TC ModelType
projectModelTypeModel modelType field =
  unimplemented ("projectModelTypeModel" <> formatErr modelType
                 <> " model " <> formatErr field)
  
extendModelTypeCtx :: Identifier -> Signature -> TC a -> TC a
extendModelTypeCtx ident msig =
  local (envSigs . at ident ?~ msig)


-- | Given a (selfified) signature, add all of its fields to the context
-- by prefixing them with the given path - presumably the path of this
-- very module.
extendModelCtx :: SelfSig -> TC a -> TC a
extendModelCtx UnitSelfSig = id
extendModelCtx (ValueSelfSig qvar ty msig) =
  -- TODO: if we are modeling joint distributions, does it ever make
  -- sense to talk about value components of other models?
  local (envGlobals . at qvar ?~ ty)
  . extendModelCtx msig
extendModelCtx (TypeSelfSig dcon tsd msig) =
  extendTypeSigDeclCtx dcon tsd
  . extendModelCtx msig
  

checkToplevel :: Toplevel -> TC Toplevel
checkToplevel (Toplevel items_) =
  Toplevel <$> go items_ return
  where
    go [] kont = kont []
    go (item:items) kont =
      checkToplevelItem item $ \item' ->
      go items $ \items' ->
      kont (item':items')

checkToplevelItem :: ToplevelItem -> (ToplevelItem -> TC a) -> TC a
checkToplevelItem item kont =
  case item of
    ToplevelModel modelIdent me ->
      let pmod = IdP modelIdent
      in inferModelExpr pmod me $ \me' msig -> do
        selfSig <- selfifyModelType pmod msig
        extendModelCtx selfSig (kont $ ToplevelModel modelIdent me')
    ToplevelModelType modelTypeIdent modType -> do
      (modType', msig) <- checkModelType modType
      extendModelTypeCtx modelTypeIdent msig
        $ kont $ ToplevelModelType modelTypeIdent modType'

-- | "Selfification" (c.f. TILT) is the process of adding to the current scope
-- a type variable of singleton kind (ie, a module variable standing
-- for a module expression) such that the module variable is given its principal
-- kind (exposes maximal sharing).
selfifyModelType :: Path -> Signature -> TC SelfSig
selfifyModelType pmod msig_ =
  case msig_ of
    UnitSig -> return UnitSelfSig
    ValueSig fld ty msig -> do
      let qvar = QVar (ProjP pmod fld)
      selfSig <- selfifyModelType pmod msig
      return $ ValueSelfSig qvar ty selfSig
    TypeSig fld bnd ->
      U.lunbind bnd $ \((tyId, U.unembed -> tsd), msig) -> do
      let p = ProjP pmod fld
          -- replace the local Con (IdP tyId) way of refering to
          -- this definition in the rest of the signature by
          -- the full projection from the model path.  Also replace the
          -- type constructors
          substitution_ = selfifyTypeSigDecl pmod tsd
          substitution = (tyId, p) : substitution_
          tsd' = U.substs substitution tsd
          msig' = U.substs substitution msig
      selfSig <- selfifyModelType pmod msig'
      return $ TypeSelfSig (Con p) tsd' selfSig
  

selfifyTypeSigDecl :: Path -> TypeSigDecl -> [(Identifier, Path)]
selfifyTypeSigDecl pmod tsd =
  case tsd of
    TypeSigDecl Nothing Nothing -> error "selfifyTypeSigDecl: impossible"
    TypeSigDecl (Just _k) Nothing -> mempty
    TypeSigDecl Nothing (Just defn) -> selfifyTypeDefn pmod defn
    TypeSigDecl (Just _) (Just _) -> error "selfifyTypeSigDecl: impossible"
