{-# LANGUAGE OverloadedStrings,
             ViewPatterns
  #-}
module Insomnia.Typecheck ( Insomnia.Typecheck.Env.runTC
                          , checkToplevel
                          ) where

import Control.Applicative ((<$>))

import Insomnia.Identifier
import Insomnia.Toplevel

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ModelType (checkModelType)
import Insomnia.Typecheck.Selfify (selfifyModelType)
import Insomnia.Typecheck.ExtendModelCtx (extendModelCtx)
import Insomnia.Typecheck.Model (inferModelExpr)

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
        extendModelSigCtx modelIdent msig
          $ extendModelCtx selfSig
          $ kont $ ToplevelModel modelIdent me'
    ToplevelModelType modelTypeIdent modType -> do
      (modType', msig) <- checkModelType modType
      extendModelTypeCtx modelTypeIdent msig
        $ kont $ ToplevelModelType modelTypeIdent modType'
