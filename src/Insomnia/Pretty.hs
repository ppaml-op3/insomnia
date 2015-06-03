{-# LANGUAGE FlexibleInstances, OverloadedStrings, ViewPatterns, TemplateHaskell #-}
module Insomnia.Pretty where

import Control.Applicative
import Control.Lens
import Control.Monad.Reader.Class

import qualified Data.Map as M
import Data.Monoid (Monoid(..), (<>), Endo(..))
import qualified Data.Set as S
import Data.String (IsString(..))
import Data.Traversable

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.Common.Literal
import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Common.Telescope
import Insomnia.Common.SampleParameters
import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr
import Insomnia.TypeDefn
import Insomnia.Module
import Insomnia.ModuleType
import Insomnia.Query
import Insomnia.Toplevel
import Insomnia.Unify

type Precedence = Int

data Associativity = AssocLeft | AssocRight | AssocNone

data PrettyCtx = PrettyCtx {
  _pcUnicode :: !Bool
  , _pcPrec :: !Precedence
  }

$(makeLenses ''PrettyCtx)

type PM a = PrettyCtx -> a

instance IsString (PrettyCtx -> Doc) where
  fromString = text

class Pretty a where
  pp :: a -> PM Doc

-- | A wrapper newtype to pretty print a "shorter" version of something.
newtype PrettyShort a = PrettyShort {unPrettyShort :: a }

ppDefault :: Pretty a => a -> Doc
ppDefault x = pp x (PrettyCtx True 0)

classify :: PM Doc
classify = ":" -- onUnicode "∷" "::"

elipsis :: PM Doc
elipsis = onUnicode "…" "..."

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
  pp m = fsep ["Map", braces $ sep (map (nesting . ppKVPair) $ M.toList m)]
    where
      ppKVPair (k, v) = pp k <+> indent (onUnicode "↦" "|->") (pp v)

                  
data PrettyMapping a b = PrettyMapping !a !b

instance (Pretty a, Pretty b) => Pretty (PrettyMapping a b) where
  pp (PrettyMapping x y) = pp x <+> "↝" <+> pp y

instance (Pretty a, Pretty b) => Pretty [PrettyMapping a b] where
  pp pms = sep $ punctuate "," (map (nesting . pp) pms)

instance Pretty () where
  pp () = text "()"

instance Pretty Int where
  pp = int

instance Pretty Integer where
  pp = integer

instance Pretty Double where
  pp = double

instance Pretty Literal where
  pp (IntL i) = pp i
  pp (RealL d) = pp d

instance Pretty Stochasticity where
  pp DeterministicParam = "parameter"
  pp RandomVariable = "random"

instance Pretty ModuleKind where
  pp ModelMK = "model"
  pp ModuleMK = "module"

instance Pretty Pattern where
  pp WildcardP = "_"
  pp (VarP v) = pp v
  pp (ConP (U.unembed -> c) (U.unembed -> minst) []) =
    case minst of
     Nothing -> pp c
     Just co -> infixOp 99 "·¢·" AssocLeft (pp c) (pp co)
  pp (ConP (U.unembed -> c) (U.unembed -> minst) ps) =
    case minst of
     Nothing -> parens $ pp c <+> (nesting $ fsep $ map pp ps)
     Just co -> parens $ infixOp 99 "·¢·" AssocLeft (pp c) (pp co) <+> (nesting $ fsep $ map pp ps)

  pp (RecordP lps) = braces $ fsep $ punctuate "," $ map ppLabeledAssign $ map (_1 %~ U.unembed) lps

instance Pretty Clause where
  pp (Clause bnd) =
    let (pat, e) = UU.unsafeUnbind bnd
    in withPrec 0 AssocNone
       $ Left $ pp pat <+> indent rightArrow (pp e)

instance Pretty Binding where
  pp (ValB av (U.unembed -> e)) =
    ppAnnVar av <+> indent "=" (pp e)
  pp (SampleB av (U.unembed -> e)) =
    ppAnnVar av <+> indent "~" (pp e)
  pp (TabB y (U.unembed -> tf)) =
    ppTabFun (pp y) tf

ppTabFun :: PM Doc  -> TabulatedFun -> PM Doc
ppTabFun ppVar (TabulatedFun bnd) =
  let (avs, TabSample sels e _ann) = UU.unsafeUnbind bnd
  in
   fsep ["forall" <+> (nesting $ fsep $ map ppAnnVar avs)
        , "in"
        , (fsep (ppVar : map pp sels)) <+> indent "~" (pp e)
        ]

ppShortTabFun :: PM Doc -> TabulatedFun -> PM Doc
ppShortTabFun ppVar (TabulatedFun bnd) =
  let (avs, TabSample sels _e _ann) = UU.unsafeUnbind bnd
  in
   fsep ["forall" <+> (nesting $ fsep $ map ppAnnVar avs)
        , "in"
        , (fsep (ppVar : map pp sels)) <+> indent "~" elipsis
        ]
  

instance Pretty TabSelector where
  pp (TabIndex v) = pp v

bindingsToList :: Bindings -> [Binding]
bindingsToList = foldMapTelescope (\x -> [x]) . bindingsTele

instance Pretty Expr where
  pp (V v) = pp v
  pp (C c) = pp c
  pp (Q q) = pp q
  pp (L l) = pp l
  pp (App e1 e2) = infixOp 10 mempty AssocLeft (pp e1) (pp e2)
  pp (Lam bnd) =
    let (av, e) = UU.unsafeUnbind bnd
    in precParens 1
       $ withPrec 0 AssocNone
       $ Left $ ppCollapseLam lambda (Endo (av:)) "." e
  pp (Ann e t) = parens $ withPrec 1 AssocNone (Left $ pp e <+> indent classify (pp t))
  pp (Record les) = braces $ fsep $ punctuate "," (map ppLabeledAssign les)
  pp (Case e clauses _ann) =
    precParens 1
    $ withPrec 0 AssocNone
    $ Left
    $ sep
    [
      fsep ["case", pp e, "of"]
    , braces $ sep $ prePunctuate ";" $ map pp clauses
    ]
  pp (Let bnd) =
    let (bindings, e) = UU.unsafeUnbind bnd
    in precParens 1
       $ withPrec 0 AssocNone
       $ Left
       $ sep
       [
         "let"
       , braces $ sep $ prePunctuate ";" $ map pp $ bindingsToList bindings
       , "in"
       , nesting (pp e)
       ]
  pp (Return e) = infixOp 10 mempty AssocLeft "return" (pp e)
  pp (Instantiate e co) = infixOp 99 "·¢·" AssocLeft (pp e) (pp co)

instance Pretty InstantiationCoercion where
  pp (InstantiationSynthesisCoercion sigma ts rho) =
    fsep [pp sigma, "≤", "[", fsep $ punctuate "," (map pp ts), "]", pp rho]

ppAnnVar :: AnnVar -> PM Doc
ppAnnVar (v, U.unembed -> (Annot mt)) =
  case mt of
    Nothing -> pp v
    Just t -> parens (pp v <+> indent classify (pp t))

ppLabeledAssign :: Pretty a => (Label, a) -> PM Doc
ppLabeledAssign (lbl, x) = pp lbl <+> indent "=" (pp x)

instance Pretty String where
  pp = text

instance Pretty QVar where
  pp (QVar m f) = pp m <> "." <> pp f

instance Pretty (U.Name a) where
  pp n = text (show n)

instance Pretty Path where
  pp (IdP identifier) = pp identifier
  pp (ProjP (IdP identifier) field) =
    pp identifier <> "." <> pp field
  pp (ProjP (TopRefP tr) field) =
    pp tr <> ":" <> pp field
  pp (ProjP path field) =
    pp path <> "." <> pp field
  pp (TopRefP tr) =
    pp tr

instance Pretty ValConPath where
  pp (ValConPath modPath vc) = pp modPath <> "." <> pp vc

instance Pretty Kind where
  pp KType = onUnicode "⋆" "*"
  pp (KArr k1 k2) = infixOp 1 rightArrow AssocRight (pp k1) (pp k2)

instance Pretty InferredValConPath where
  pp (InferredValConPath tp f) = pp tp <> "@" <> pp f

instance Pretty ValueConstructor where
  pp (VCLocal n) = pp n
  pp (VCGlobal (Left p)) = pp p
  pp (VCGlobal (Right p)) = pp p

instance Pretty TypePath where
  pp (TypePath pmod f) = pp pmod <> "." <> pp f

ppTypePathNoRoot :: TypePath -> PM Doc
ppTypePathNoRoot (TypePath pmod f) =
  ppPathNoRoot pmod <> "." <> pp f

ppPathNoRoot :: Path -> PM Doc
ppPathNoRoot (IdP _) = mempty
ppPathNoRoot (TopRefP _) = mempty
ppPathNoRoot (ProjP (IdP _) f) = pp f
ppPathNoRoot (ProjP p f) = ppPathNoRoot p <> "." <> pp f

instance Pretty TypeConstructor where
  pp (TCLocal n) = pp n
  pp (TCGlobal p) = pp p

instance Pretty Type where
  pp (TV v) = pp v
  pp (TUVar u) = pp u
  pp (TApp
      (TApp
       (TC (TCLocal (U.name2String -> "->")))
       t1)
      t2) =
    -- hack
    infixOp 1 rightArrow AssocRight (pp t1) (pp t2)
  pp (TApp t1 t2) = infixOp 2 mempty AssocLeft (pp t1) (pp t2)
  pp (TC c) = pp c
  pp (TAnn t k) = parens $ fsep [pp t, nesting $ classify <+> pp k]
  pp (TForall bnd) =
    -- todo: do this safely; collapse consecutive foralls
    let (vk, t) = UU.unsafeUnbind bnd
    in ppCollapseForalls (Endo (vk :)) t
  pp (TRecord row) = pp row

instance Pretty Row where
  pp (Row ts) = braces . fsep . punctuate ";" $ map ppLabeledType ts

instance Pretty Label where
  pp (Label n) = pp n

ppLabeledType :: (Label, Type) -> PM Doc
ppLabeledType (label, ty) = fsep [pp label, indent classify (pp ty)]

ppCollapseForalls :: Endo [(TyVar, Kind)] -> Type -> PM Doc
ppCollapseForalls front t =
  case t of
    TForall bnd ->
      let (vk, t') = UU.unsafeUnbind bnd
      in ppCollapseForalls (front <> Endo (vk :)) t'
    _ -> do
      let tvks = appEndo front []
      fsep ([onUnicode "∀" "forall"]
            ++ map ppVarBind tvks
            ++ [nesting ("." <+> withPrec 0 AssocNone (Left $ pp t))])
  where
    ppVarBind (v,k) =
      parens $ withPrec 2 AssocNone (Left $ fsep [pp v, classify, pp k])

ppCollapseLam :: PM Doc -> Endo [AnnVar] -> PM Doc -> Expr -> PM Doc
ppCollapseLam lam mavs dot e_ =
  case e_ of
    Lam bnd ->
      let (av, e1) = UU.unsafeUnbind bnd
      in ppCollapseLam lam (mavs <> Endo (av :)) dot e1
    _ -> do
      let
        avs = appEndo mavs []
      fsep [lam,
            nesting $ fsep (map ppAnnVar avs),
            indent dot (pp e_)]

ppDataDefn :: Field -> DataDefn -> PM Doc
ppDataDefn d bnd =
  let (vks, constrDefs) = UU.unsafeUnbind bnd
  in "data" <+> (nesting $ fsep
                 [
                   pp d
                 , ppTyVarBindings vks
                 , indent "=" (ppConstrDefs constrDefs)
                 ])
  where
    ppConstrDefs = sep . prePunctuate "|" . map ppConstructorDef
    ppConstructorDef (ConstructorDef c ts) =
      pp c <+> nesting (fsep $ map pp ts)

ppTyVarBindings :: [(TyVar, Kind)] -> PM Doc
ppTyVarBindings = fsep . map ppTyVarBinding
  where
    ppTyVarBinding (v,k) = parens (pp v <+> indent classify (pp k))


instance Pretty Decl where
  pp (TypeDefn c td) = ppTypeDefn c td
  pp (ValueDecl f vd) = ppValueDecl f vd
  pp (ImportDecl p) = ppImportDecl p
  pp (TypeAliasDefn f a) = ppTypeAlias f a
  pp (SubmoduleDefn f m) = ppModule (pp f) m
  pp (SampleModuleDefn f m) = fsep ["module", pp f, indent "~" (pp m)]

instance Pretty (PrettyShort Decl) where
  pp (PrettyShort (TypeDefn c td)) = ppShortTypeDefn c td
  pp (PrettyShort (ImportDecl p)) = ppImportDecl p
  pp (PrettyShort (ValueDecl f vd)) = ppShortValueDecl f vd
  pp (PrettyShort (TypeAliasDefn f _a)) =
    "type" <+> pp f <+> "=" <+> elipsis
  pp (PrettyShort (SubmoduleDefn f _m)) =
    "module" <+> pp f <+> "=" <+> elipsis
  pp (PrettyShort (SampleModuleDefn f _m)) =
    "module" <+> pp f <+> "~" <+> elipsis
    
instance Pretty (PrettyField TypeDefn) where
  pp (PrettyField fld defn) = ppTypeDefn fld defn

instance Pretty (PrettyField TypeAlias) where
  pp (PrettyField fld alias) = ppTypeAlias fld alias

ppImportDecl :: Path -> PM Doc
ppImportDecl p = fsep ["import", pp p]

ppTypeDefn :: Field -> TypeDefn -> PM Doc
ppTypeDefn c (DataDefn d) = ppDataDefn c d
ppTypeDefn c (EnumDefn n) = "enum" <+> pp c <+> pp n

ppShortTypeDefn :: Field -> TypeDefn -> PM Doc
ppShortTypeDefn c (DataDefn _) = "data" <+> pp c <+> elipsis
ppShortTypeDefn c (EnumDefn n) = "enum" <+> pp c <+> pp n

ppTypeAlias :: Field -> TypeAlias -> PM Doc
ppTypeAlias c (ManifestTypeAlias bnd) =
  let (tvks, ty) = UU.unsafeUnbind bnd
  in "type" <+>  (nesting $ fsep
                  [
                    pp c
                  , ppTyVarBindings tvks
                  , indent "=" (pp ty)
                  ])
ppTypeAlias c (DataCopyTypeAlias tp defn) =
  let (pfx, mcons) =
        case defn of
         DataDefn dd -> ("data",
                         nesting $ parens $ ppDataDefn "_" dd)
         EnumDefn {} -> ("enum", mempty)
  in pfx <> "type" <+> (nesting $ fsep
                 [
                   pp c
                 , indent "=" (fsep [pfx, pp tp])
                 , mcons
                 ])


ppValueDecl :: Field -> ValueDecl -> PM Doc
ppValueDecl v (SigDecl s t) = pp s <+> "sig" <+> pp v <+> indent classify (pp t)
ppValueDecl v (FunDecl f) = ppFunDecl v f 
ppValueDecl v (ParameterDecl e) = "parameter" <+> pp v <+> "=" <+> pp e
ppValueDecl v (ValDecl e) = ppValSampleDecl "=" v e
ppValueDecl v (SampleDecl e) = ppValSampleDecl "~" v e
ppValueDecl v (TabulatedSampleDecl tabfun) = ppTabFun (pp v) tabfun

ppShortValueDecl :: Field -> ValueDecl -> PM Doc
ppShortValueDecl v (SigDecl stoch t) = pp stoch <+> "sig" <+> pp v <+> indent classify (pp t)
ppShortValueDecl f (FunDecl _e) = "fun" <+> pp f <+> elipsis <+> "=" <+> elipsis
ppShortValueDecl f (ParameterDecl _e) = "parameter" <+> pp f <+> "=" <+> elipsis
ppShortValueDecl f (ValDecl _e) = "val" <+> pp f <+> "=" <+> elipsis
ppShortValueDecl f (SampleDecl _e) = "val" <+> pp f <+> "~" <+> elipsis
ppShortValueDecl v (TabulatedSampleDecl tabfun) = ppShortTabFun (pp v) tabfun

ppFunDecl :: Field -> Function -> PM Doc
ppFunDecl v_ (Function e_) =
  case e_ of
   Left e -> ppFunLam v_ e
   Right (Generalization bnd _co) ->
     let (_tvks, e) = UU.unsafeUnbind bnd
     in ppFunLam v_ e
  where
    ppFunLam :: Field -> Expr -> PM Doc
    ppFunLam v e =
      case e of
       Lam bnd ->
         let (av, e1) = UU.unsafeUnbind bnd
         in ppCollapseLam ("fun" <+> pp v) (Endo (av :)) "=" e1
       _ -> "fun" <+> pp v <+> indent "=" (pp e)

ppValSampleDecl :: PM Doc -> Field -> Expr -> PM Doc
ppValSampleDecl sym v e =
  "val" <+> pp v <+> indent sym (pp e)

instance Pretty Module where
  pp (Module decls) =
    fsep ["{"
         , vcat $ map (nesting . pp) decls
         , "}"]

instance Pretty Toplevel where
  pp (Toplevel items) =
    vcat $ punctuate "\n" $ map pp items

ppModule :: PM Doc -> ModuleExpr -> PM Doc
ppModule ppName moduleExpr =
  case moduleExpr of
    ModuleSeal moduleExpr'@(ModuleStruct {}) moduleSig ->
      fsep ["module", ppName
           , indent classify (pp moduleSig)
           , nesting (pp moduleExpr')
           ]
    ModuleFun bnd ->
      fsep ["module", ppName, ppFunctor "=" bnd]
    _ ->
      fsep ["module", ppName, indent "=" (pp moduleExpr)]

instance Pretty ToplevelItem where
  pp (ToplevelModule identifier mdl) = ppModule (pp identifier) mdl
  pp (ToplevelModuleType identifier moduleType) =
    fsep ["module", "type", pp identifier, pp moduleType]
  pp (ToplevelImported filePath topref subordinateToplevel) =
    fsep ["import", pp topref, pp (show filePath), "{", nesting $ pp subordinateToplevel, "}"]
  pp (ToplevelQuery qe) =
    fsep ["query", pp qe]

instance Pretty ModuleExpr where
  pp (ModuleStruct mdl) = "module" <+> pp mdl
  pp (ModuleModel mdl) = "model" <+> pp mdl
  pp (ModuleSeal mdl moduleSig) =
    parens (fsep [pp mdl, indent classify (pp moduleSig)])
  pp (ModuleAssume mtype) = fsep ["assume", nesting (pp mtype)]
  pp (ModuleId modPath) = pp modPath
  pp (ModuleFun bnd) = ppFunctor rightArrow bnd
  pp (ModuleApp pfun args) =
    fsep [pp pfun, parens $ fsep $ punctuate "," $ map pp args]

ppFunctor :: (U.Alpha a, Pretty a)
             => PM Doc
             -> U.Bind (Telescope (FunctorArgument ModuleType)) a
             -> PM Doc
ppFunctor sym bnd =
    let (argsTele, body) = UU.unsafeUnbind bnd
    in fsep [parens (fsep $ ppTelescope pp argsTele), indent sym (pp body)]
  

instance Pretty ModelExpr where
  pp (ModelId p) = pp p
  pp (ModelStruct mdl) = pp mdl
  pp (ModelLocal (Module hid) body ty) =
    fsep ["local",
          nesting (fsep $ map pp hid),
          "in",
          nesting (fsep [pp body, indent classify (pp ty)])]

instance Pretty ToplevelSummary where
  pp UnitTS = mempty
  pp (ModuleTS fld bnd) =
    let ((ident, U.unembed -> modTy), rest) = UU.unsafeUnbind bnd
    in fsep ["module", pp fld, classify , pp modTy]
       $$ pp rest
  pp (SignatureTS fld bnd) =
    let ((ident, U.unembed -> modTy), rest) = UU.unsafeUnbind bnd
    in fsep ["module", "type", pp fld, "=", pp modTy]
       $$ pp rest

instance Pretty ModuleType where
  pp (SigMT sigv) = pp sigv
  pp (FunMT bnd) =
    let (tele, body) = UU.unsafeUnbind bnd
    in fsep [parens (fsep $ ppTelescope pp tele), indent rightArrow (pp body)]
  pp (IdentMT ident) = pp ident
  pp (WhereMT mt wh) =
    fsep [pp mt, indent "where" (pp wh)]
  pp (TopRefMT t fld) =
    pp t <> ":" <> pp fld

instance Pretty WhereClause where
  pp (WhereTypeCls bnd rhs) =
    let (_, p) = UU.unsafeUnbind bnd
    in fsep ["type", ppTypePathNoRoot p, indent "=" (pp rhs)]

instance Pretty ModuleTypeNF where
  pp (SigMTNF sigv) = pp sigv
  pp (FunMTNF bnd) =
    let (tele, body) = UU.unsafeUnbind bnd
    in fsep [parens (fsep $ ppTelescope pp tele), indent rightArrow (pp body)]

instance Pretty a => Pretty (FunctorArgument a) where
  pp (FunctorArgument ident (U.unembed -> modK) (U.unembed -> t)) =
    fsep [pp modK, pp ident, indent classify (pp t)]

instance Pretty a => Pretty (SigV a) where
  pp (SigV x modK) = fsep [pp modK, "{", pp x, "}" ]

instance Pretty Signature where
  pp UnitSig = mempty
  pp (ValueSig fld ty sig) =
    fsep ["val", text fld, indent classify (pp ty)]
    $$ pp sig
  pp (TypeSig fld bnd) =
    let ((tv, U.unembed -> tsd), sig) = UU.unsafeUnbind bnd
    in (case tsd of
           ManifestTypeSigDecl defn -> ppTypeDefn fld defn
           AbstractTypeSigDecl k ->
             fsep ["type", pp tv, indent classify (pp k)]
           AliasTypeSigDecl a ->
             ppTypeAlias fld a)
       $$ pp sig
  pp (SubmoduleSig _fld bnd) =
    let ((mId, U.unembed -> mTy), sig) = UU.unsafeUnbind bnd
    in fsep ["module", pp mId, indent classify (pp mTy)]
       $$ pp sig

instance Pretty QueryExpr where
  pp (GenSamplesQE p params) =
    fsep ["sample", pp p, pp (params^.numSamplesParameter)]

instance Pretty (UVar w a) where
  pp = text . show

instance Pretty (S.Set (UVar w a)) where
  pp s = braces $ fsep $ punctuate "," (map pp $ S.toList s)

instance Pretty a => Pretty (UnificationFailure TypeUnificationError w a) where
  pp (CircularityOccurs uv t) =
    text "occurs check failed: the variable"
    <+> pp uv <+> "occurs in" <+> pp t
  pp (Unsimplifiable (SimplificationFail constraintMap t1 t2)) =
    cat ["failed to simplify unification problem "
         <+> pp t1 <+> indent "≟" (pp t2)
        , "under constraints"
        , pp constraintMap]
  pp (Unsimplifiable (RowLabelsDifferFail r1 r2)) =
    cat ["failed to simplify unification problem "
         <+> pp r1 <+> indent "≟" (pp r2)
         <+> " because the rows have different labels"]
    

-- | @ppTelescope pelem t@ pretty prints the 'Telescope' @t@
-- using @pelem@ to print each element.
ppTelescope :: U.Alpha p => (p -> PM Doc) -> Telescope p -> [PM Doc]
ppTelescope pelem t =
  foldMapTelescope (\x -> [pelem x]) t

-- onUnicode' :: String -> String -> PM Doc
-- onUnicode' yes no = onUnicode (text yes) (text no)

-- | @onUnicode yes no@ runs @yes@ if Unicode output is desirable,
-- otherwise runs @no@.
onUnicode :: PM a -> PM a -> PM a
onUnicode yes no = do
  inUnicode <- view pcUnicode
  if inUnicode then yes else no

lambda :: PM Doc
lambda = onUnicode "λ" "\\"

rightArrow :: PM Doc
rightArrow = onUnicode "→" "->"

-- ============================================================
-- Precedence

infixOp :: Precedence -- ^ precedence of the operator
           -> PM Doc -- ^ operator
           -> Associativity -- ^ operator associativity
           -> PM Doc -- ^ lhs pretty printer
           -> PM Doc -- ^ rhs pretty printer
           -> PM Doc
infixOp precOp opr assoc lhs rhs =
  precParens precOp $ fsep [ withPrec precOp assoc (Left lhs),
                             opr,
                             nesting $ withPrec precOp assoc (Right rhs)]

precParens :: Precedence -> PM Doc -> PM Doc
precParens prec d = do
  prec' <- view pcPrec
  if (prec > prec')
    then d
    else parens d

withPrec :: Precedence
         -> Associativity
         -> Either (PM a) (PM a)
         -> PM a
withPrec prec assoc lOrR =
  let
    fromEither :: Either a a -> a
    fromEither = either id id

    (penalty, doc) =
      case (assoc, lOrR) of
        (AssocLeft, Left l) -> (-1, l)
        (AssocRight, Right l) -> (-1, l)
        (_, _) -> (0, fromEither lOrR)
  in local (pcPrec .~ (prec + penalty)) $ doc

-- ============================================================
-- Lifted versions of the PrettyPrint combinators

(<+>) :: PM Doc -> PM Doc -> PM Doc
d1 <+> d2 = (PP.<+>) <$> d1 <*> d2

($$) :: PM Doc -> PM Doc -> PM Doc
da $$ db = (PP.$$) <$> da <*> db

space :: PM Doc
space = pure PP.space

parens :: PM Doc -> PM Doc
parens = fmap PP.parens

braces :: PM Doc -> PM Doc
braces = fmap PP.braces

brackets :: PM Doc -> PM Doc
brackets = fmap PP.brackets
  
text :: String -> PM Doc
text = pure . PP.text

int :: Int -> PM Doc
int = pure . PP.int

integer :: Integer -> PM Doc
integer = pure . PP.integer

double :: Double -> PM Doc
double = pure . PP.double

fsep :: [PM Doc] -> PM Doc
fsep ds = PP.fsep <$> sequenceA ds

sep :: [PM Doc] -> PM Doc
sep ds = PP.sep <$> sequenceA ds

cat :: [PM Doc] -> PM Doc
cat ds = PP.cat <$> sequenceA ds

vcat :: [PM Doc] -> PM Doc
vcat ds = PP.vcat <$> sequenceA ds

fcat :: [PM Doc] -> PM Doc
fcat ds = PP.fcat <$> sequenceA ds

punctuate :: PM Doc -> [PM Doc] -> [PM Doc]
punctuate _s [] = []
punctuate s (x:xs) = go x xs
  where go y [] = [y]
        go y (z:zs) = (y <> s) : go z zs

-- like 'punctuate' but attaches the separator to preceed items instead of after.
-- Also uses '(<+>)' 
prePunctuate :: PM Doc -> [PM Doc] -> [PM Doc]
prePunctuate _s [] = []
prePunctuate s (x:xs) = go x xs
  where go y [] = [y]
        go y (z:zs) = y : go (s <+> z) zs


nesting :: PM Doc -> PM Doc
nesting = fmap (PP.nest nestingLevel)
  where
    nestingLevel = 2

-- | Writes:
-- @
--   foo
--     <delim> <bar>
-- @
indent :: PM Doc -> PM Doc -> PM Doc
indent delim d = nesting (delim <+> d)
