module Insomnia.ToF.Builtins where

import Control.Monad

import qualified Unbound.Generics.LocallyNameless as U

import Insomnia.Common.ModuleKind
import Insomnia.Identifier
import Insomnia.ModuleType
import Insomnia.Types (Type)
import Insomnia.Expr (QVar(..))

import qualified FOmega.Syntax as F
import qualified FOmega.SemanticSig as F
import qualified FOmega.SubSig as F

import Insomnia.ToF.Env
import Insomnia.ToF.Type (type')
import Insomnia.ToF.ModuleType (mkAbstractModuleSig)

looksLikeBuiltin :: Maybe Path -> ModuleType -> Maybe [(QVar, Type)]
looksLikeBuiltin (Just p) (SigMT (SigV sig ModuleMK)) =
   looksLikeBuiltinSig p sig
-- looksLikeBuiltin _ _ = Nothing

looksLikeBuiltinSig :: Path -> Signature -> Maybe [(QVar, Type)]
looksLikeBuiltinSig p UnitSig = return []
looksLikeBuiltinSig p (TypeSig {}) = mzero
looksLikeBuiltinSig p (SubmoduleSig {}) = mzero
looksLikeBuiltinSig p (ValueSig f t rest) = do
  let q = QVar p f
  guard (looksLikeBuiltinQVar q)
  rest' <- looksLikeBuiltinSig p rest
  return $ (q,t):rest'

looksLikeBuiltinQVar :: QVar -> Bool
looksLikeBuiltinQVar q = True

builtinNameFromQVar :: QVar -> F.Var
builtinNameFromQVar (QVar p f) =
  U.s2n $ p2s $ ProjP p f
  where
    p2s (IdP nm) = U.name2String nm
    p2s (ProjP p' f') = p2s p' ++ "." ++ f'

makeBuiltinsModule :: ToF m
                      => [(QVar, Type)]
                      -> m (F.AbstractSig, F.Term)
makeBuiltinsModule qts = do
  (sig, fields) <- liftM unzip $ forM qts $ \(q@(QVar _ f), ty) -> do
    (ty', _) <- type' ty
    let fld = F.FUser f
        qv = builtinNameFromQVar q
        m = F.V qv -- builtins looks like funny free names.
    return ((fld, F.ValSem ty'), (fld, F.valSemTerm m))
  return (mkAbstractModuleSig ([], sig), F.Record fields)

