module Insomnia.ToF.Toplevel where

import Control.Lens
import Control.Monad.Reader
import Data.Monoid (Monoid(..), (<>), Endo(..))
import qualified Data.Map as M

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Identifier
import Insomnia.Toplevel
import Insomnia.Query
import Insomnia.ModuleType
import Insomnia.Module

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Summary
import Insomnia.ToF.ModuleType (moduleType)
import Insomnia.ToF.Module (moduleExpr)
import Insomnia.ToF.Query (queryExpr)

type TopSummary = ModSummary' F.Command

toplevel :: ToF m => Toplevel -> m F.Command
toplevel (Toplevel its) =
  toplevelItems its $ \(summary@(tvks,sig), fields, cmdHole) -> do
    let semSig = F.ModSem sig
    ty <- F.embedSemanticSig semSig
    let r = F.Record fields
        m = F.ReturnC $ F.packs (map (F.TV . fst) tvks) r (tvks, ty)
    return ({-mkAbstractModuleSig summary,-} appEndo cmdHole m)

toplevelItems :: ToF m => [ToplevelItem] -> (TopSummary -> m ans) -> m ans
toplevelItems [] kont = kont mempty
toplevelItems (it:its) kont = let
  kont1 out1 = toplevelItems its $ \outs -> kont $ out1 <> outs
  in case it of
      ToplevelModule ident me -> toplevelModule ident me kont1
      ToplevelModuleType sigIdent modTy -> toplevelModuleType sigIdent modTy kont1
      ToplevelQuery qe -> toplevelQuery qe kont1

toplevelModule :: ToF m => Identifier -> ModuleExpr -> (TopSummary -> m ans) -> m ans
toplevelModule ident me kont = do
  (F.AbstractSig bnd, msub) <- moduleExpr (Just $ IdP ident) me
  U.lunbind bnd $ \(tvks, modsig) -> do
    let nm = U.name2String ident
        xv = U.s2n nm
    local (modEnv %~ M.insert ident (modsig, xv)) $ do
      let tvs = map fst tvks
      munp <- F.unpacksCM tvs xv
      let c = Endo $ munp msub
          thisOne = ((tvks, [(F.FUser nm, modsig)]),
                     [(F.FUser nm, F.V xv)],
                     c)
      kont thisOne

toplevelModuleType :: ToF m => SigIdentifier -> ModuleType -> (TopSummary -> m ans) -> m ans
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
        c = Endo (F.LetC . U.bind (xv, U.embed $ F.Record [(F.FSig, mId)]))
        thisOne = (([], [(F.FUser nm, semSig)]),
                   [(F.FUser nm, F.V xv)],
                   c)
    kont thisOne

toplevelQuery :: ToF m => QueryExpr -> (TopSummary -> m ans) -> m ans
toplevelQuery qe kont = do
  cmd <- queryExpr qe
  let xv = U.s2n "_"
      c = Endo (F.BindC . U.bind (xv, U.embed $ cmd))
      thisOne = (mempty,
                 mempty,
                 c)
  kont thisOne

