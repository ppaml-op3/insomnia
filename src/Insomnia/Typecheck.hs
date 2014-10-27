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
import Insomnia.Typecheck.Selfify (selfifyModelType, selfifyTypeDefn)
import Insomnia.Typecheck.Model (inferModelExpr)
import Insomnia.Typecheck.SelfSig (SelfSig(..))

-- | Find a model with the given name in the context, return its
-- type.
lookupModel :: Path -> TC ModelType
lookupModel (IdP identifier) =
  unimplemented $ "lookupModel with identifier " <> formatErr identifier
lookupModel (ProjP model field) = do
  s <- lookupModel model
  projectModelTypeModel s field

projectModelTypeModel :: ModelType -> Field -> TC ModelType
projectModelTypeModel modelType field =
  unimplemented ("projectModelTypeModel" <> formatErr modelType
                 <> " model " <> formatErr field)
  
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
