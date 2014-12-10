{-# LANGUAGE OverloadedStrings,
             ViewPatterns
  #-}
module Insomnia.Typecheck ( Insomnia.Typecheck.Env.runTC
                          , checkToplevel
                          ) where

import Data.Monoid ((<>))
import Control.Applicative ((<$>))

import Insomnia.Identifier
import Insomnia.Toplevel

import Insomnia.Typecheck.Env
import Insomnia.Typecheck.ModuleType (checkModuleType)
import Insomnia.Typecheck.Selfify (selfifyModuleType)
import Insomnia.Typecheck.ExtendModuleCtx (extendModuleCtx)
import Insomnia.Typecheck.Module (inferModuleExpr)

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
    ToplevelModule moduleIdent me ->
      let pmod = IdP moduleIdent
      in inferModuleExpr pmod me $ \me' msig modK -> do
        selfSig <- selfifyModuleType pmod msig
                   <??@ "while selfifying module " <> formatErr moduleIdent
        extendModuleSigCtx moduleIdent msig modK
          $ extendModuleCtx selfSig
          $ kont $ ToplevelModule moduleIdent me'
          
    ToplevelModuleType modTypeIdent modType -> do
      (modType', msig, modK) <- checkModuleType modType
                          <??@ ("while checking module type "
                                <> formatErr modTypeIdent)
      extendModuleTypeCtx modTypeIdent msig modK
        $ kont $ ToplevelModuleType modTypeIdent modType'
        
