module Insomnia.ToF.Toplevel where

import Control.Lens
import Control.Monad.Reader
import Data.Monoid (Monoid(..), (<>), Endo(..))
import qualified Data.Map as M

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Toplevel
import Insomnia.ModuleType
import Insomnia.Module

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Summary
import Insomnia.ToF.ModuleType (moduleType, mkAbstractModuleSig)
import Insomnia.ToF.Module (moduleExpr)

toplevel :: ToF m => Toplevel -> m F.Term
toplevel (Toplevel its) =
  toplevelItems its $ \(summary@(tvks,sig), fields, termHole) -> do
    let semSig = F.ModSem sig
    ty <- F.embedSemanticSig semSig
    let r = F.Record fields
        m = F.Return $ F.packs (map (F.TV . fst) tvks) r (tvks, ty)
    return ({-mkAbstractModuleSig summary,-} appEndo termHole m)

toplevelItems :: ToF m => [ToplevelItem] -> (ModSummary -> m ans) -> m ans
toplevelItems [] kont = kont mempty
toplevelItems (it:its) kont = let
  kont1 out1 = toplevelItems its $ \outs -> kont $ out1 <> outs
  in case it of
      ToplevelModule ident me -> toplevelModule ident me kont1
      ToplevelModuleType sigIdent modTy -> toplevelModuleType sigIdent modTy kont1

toplevelModule :: ToF m => Identifier -> ModuleExpr -> (ModSummary -> m ans) -> m ans
toplevelModule ident me kont = do
  (F.AbstractSig bnd, msub) <- moduleExpr me
  U.lunbind bnd $ \(tvks, modsig) -> do
    let nm = U.name2String ident
        xv = U.s2n nm
    local (modEnv %~ M.insert ident (modsig, xv)) $ do
      let tvs = map fst tvks
      munp <- F.unpacksM tvs xv
      let m = Endo $ munp msub
          thisOne = ((tvks, [(F.FUser nm, modsig)]),
                     [(F.FUser nm, F.V xv)],
                     m)
      kont thisOne

toplevelModuleType :: ToF m => SigIdentifier -> ModuleType -> (ModSummary -> m ans) -> m ans
toplevelModuleType sigIdent modTy kont = do
  absSig@(F.AbstractSig bnd) <- moduleType modTy
  absTy <- F.embedAbstractSig absSig
  let semSig = F.SigSem absSig
  let nm = U.name2String sigIdent
      xv = U.s2n nm
  local (sigEnv %~ M.insert sigIdent absSig) $ do
    let mId = let
          z = U.s2n "z"
          in F.Lam $ U.bind (z, U.embed absTy) $ F.V z
        m = Endo (F.Let . U.bind (xv, U.embed $ F.Record [(F.FSig, mId)]))
        thisOne = (([], [(F.FUser nm, semSig)]),
                   [(F.FUser nm, F.V xv)],
                   m)
    kont thisOne
