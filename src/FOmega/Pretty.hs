{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module FOmega.Pretty where

import Data.Monoid (Monoid(..), (<>))

import Text.PrettyPrint (Doc)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Pretty

import {-# SOURCE #-} FOmega.Syntax

ppField :: Field -> PM Doc
ppField FVal = "val"
ppField FType = "type"
ppField FSig = "sig"
ppField FData = "data"
ppField FCon = "con"
ppField (FTuple i) = "#" <> int i
ppField (FUser s) = text s

ppKind :: Kind -> PM Doc
ppKind KType = onUnicode "⋆" "*"
ppKind (KArr k1 k2) = infixOp 1 rightArrow AssocRight (ppKind k1) (ppKind k2)

ppType :: Type -> PM Doc
ppType t_ =
  case t_ of
   (TArr t1 t2) -> infixOp 1 rightArrow AssocRight (ppType t1) (ppType t2)
   TV v -> pp v
   TApp t1 t2 -> infixOp 2 mempty AssocLeft (ppType t1) (ppType t2)
   TLam bnd ->
     let ((tv, U.unembed -> k), body) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep [lambda, pp tv, coloncolon, ppKind k,
                indent "." (withPrec 0 AssocNone $ Left $ ppType body)]
   TForall bnd ->
     let ((tv, U.unembed -> k), body) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep [onUnicode "∀" "forall", pp tv, coloncolon, ppKind k,
                indent "." (withPrec 0 AssocNone $ Left $ ppType body)]
   TExist bnd ->
     let ((tv, U.unembed -> k), body) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep [onUnicode "∃" "exist", pp tv, coloncolon, ppKind k,
                indent "." (withLowestPrec $ ppType body)]
   TRecord fts ->
     let
       ppF (f, t) = fsep [ppField f, indent coloncolon (ppType t)]
     in braces $ fsep $ punctuate "," $ map ppF fts
   TSum fts ->
     let
       ppF (f, t) = fsep [ppField f, indent coloncolon (ppType t)]
     in
      braces $ fsep $ prePunctuate "|" $ map ppF fts
   TDist t ->
     fsep ["Dist", indent mempty (ppType t)]
        
withLowestPrec :: PM Doc -> PM Doc
withLowestPrec = withPrec 0 AssocNone . Left

ppTerm :: Term -> PM Doc
ppTerm m_ =
  case m_ of
   V v -> pp v
   L l -> pp l
   Lam bnd ->
     let ((v, U.unembed -> t), body) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep [onUnicode "λ" "\\", parens $ fsep [pp v, coloncolon, ppType t],
              indent "." (withLowestPrec $ ppTerm body)]
   App m1 m2 ->
     infixOp 2 mempty AssocLeft (ppTerm m1) (ppTerm m2)
   PLam bnd -> 
     let ((v, U.unembed -> k), body) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep [onUnicode "λ" "\\", brackets $ fsep [pp v, coloncolon, ppKind k],
              indent "." (withLowestPrec $ ppTerm body)]
   PApp m t ->
     fsep [withPrec 2 AssocRight $ Left $ ppTerm m, brackets $ ppType t]
   Pack t m ep ->
     precParens 2
     $ fsep ["pack", ppType t, indent "," (ppTerm m),
             indent "as" (ppExistPack ep)]
   Unpack bnd ->
     let ((tv, xv, U.unembed -> m), body) = UU.unsafeUnbind bnd
     in precParens 2
        $ fsep ["unpack", pp tv, ",", pp xv,
                indent "=" (withPrec 2 AssocNone $ Left $ ppTerm m),
                "in" <+> (ppTerm body)]
   Record fms ->
     let
       ppF (f, m) = fsep [ppField f, indent "=" (ppTerm m)]
     in braces $ fsep $ punctuate "," $ map ppF fms
   Proj m f ->
     withPrec 2 AssocLeft (Left $ ppTerm m) <> "." <> ppField f
   Inj f m t ->
     precParens 2
     $ fsep ["inj", ppField f, ppTerm m, "as" <+> (ppType t)]
   Let bnd ->
     let ((x, U.unembed -> m1), m2) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep ["let", pp x, indent "=" (withPrec 2 AssocNone $ Left $ ppTerm m1),
                "in" <+> (withLowestPrec $ ppTerm m2)]
   Case m clauses optDefault ->
     precParens 1
     $ fsep ["case", pp m, "of",
             braces $ sep $ prePunctuate ";" (map ppClause clauses
                                              ++ ppDefaultClause optDefault)]
   Return m ->
     fsep ["return", ppTerm m]
   LetSample bnd ->
     let ((x, U.unembed -> m1), m2) = UU.unsafeUnbind bnd
     in precParens 1
        $ fsep ["let", pp x, indent "~" (withPrec 2 AssocNone $ Left $ ppTerm m1),
                "in" <+> (withLowestPrec $ ppTerm m2)]
   Assume t ->
     fsep ["assume", ppType t]
   Abort t ->
     fsep ["abort", ppType t]

ppClause :: Clause -> PM Doc
ppClause (Clause bnd) =
  let ((U.unembed -> f, v), m) = UU.unsafeUnbind bnd
  in
   fsep [parens $ fsep [ppField f, pp v], indent "→" (withLowestPrec $ ppTerm m)]

ppDefaultClause :: Maybe Term -> [PM Doc]
ppDefaultClause Nothing = []
ppDefaultClause (Just m) = [fsep ["_", indent "→" (withLowestPrec $ ppTerm m)]]

ppExistPack :: ExistPack -> PM Doc
ppExistPack bnd =
  let ((tv, U.unembed -> k), t) = UU.unsafeUnbind bnd
  in fsep [ pp tv, coloncolon, ppKind k,
            indent "." (ppType t) ]
