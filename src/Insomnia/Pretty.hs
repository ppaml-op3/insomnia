{-# LANGUAGE FlexibleInstances, OverloadedStrings, TemplateHaskell #-}
module Insomnia.Pretty where

import Control.Applicative
import Control.Lens
import Control.Monad.Reader.Class

import Data.Monoid (Monoid(..))
import Data.String (IsString(..))
import Data.Traversable

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc)

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Unsafe as UU

import Insomnia.AST
import Insomnia.Types
import Insomnia.Unify

type Precedence = Int

data Associativity = AssocLeft | AssocRight | AssocNone

data PrettyCtx = PrettyCtx {
  _pcUnicode :: Bool
  , _pcPrec :: Precedence
  }

$(makeLenses ''PrettyCtx)

type PM a = PrettyCtx -> a

instance IsString (PrettyCtx -> Doc) where
  fromString = text

class Pretty a where
  pp :: a -> PM Doc

ppDefault :: Pretty a => a -> Doc
ppDefault x = pp x (PrettyCtx True 0)

instance Pretty Int where
  pp = int

instance Pretty Integer where
  pp = integer

instance Pretty Expr where
  pp = text . show

instance Pretty Pattern where
  pp = text . show  

instance Pretty Con where
  pp = text . unCon

instance Pretty (U.Name a) where
  pp = text . show

instance Pretty Kind where
  pp KType = onUnicode "⋆" "*"
  pp (KArr k1 k2) = infixOp 0 "→" "->" AssocRight (pp k1) (pp k2)

instance Pretty Type where
  pp (TV v) = pp v
  pp (TUVar u) = pp u
  pp (TApp
      (TApp
       (TC (Con "->"))
       t1)
      t2) =
    -- hack
    infixOp 1 "→" "->" AssocRight (pp t1) (pp t2)
  pp (TApp t1 t2) = infixOp 2 mempty mempty AssocLeft (pp t1) (pp t2)
  pp (TC c) = pp c
  pp (TAnn t k) = parens $ fsep [pp t, nesting $ onUnicode "∷" "::" <+> pp k]
  pp (TForall bnd) =
    -- todo: do this safely; collapse consecutive foralls
    let ((v,k), t) = UU.unsafeUnbind bnd
    in fsep [onUnicode "∀" "forall"
            , parens $ withPrec 2 AssocNone (Left $ fsep [pp v
                                                         , onUnicode "∷" "::"
                                                         , pp k])
            , nesting ("." <+> withPrec 0 AssocNone (Left $ pp t))
            ]

instance Pretty DataDecl where
  pp = text . show

instance Pretty Decl where
  pp (SigDecl v t) = "sig" <+> pp v <+> nesting ((onUnicode "∷" "::") <+> pp t)
  pp (FunDecl v e) = "fun" <+> pp v <+> nesting ("=" <+> pp e)
  pp (DataDecl c d) = "data" <+> pp c <+> pp d
  pp (EnumDecl c n) = "enum" <+> pp c <+> pp n

instance Pretty Module where
  pp (Module decls) =
    cat $ map pp decls

instance Pretty (UVar a) where
  pp = text . show

instance Pretty a => Pretty (UnificationFailure TypeUnificationError a) where
  pp (CircularityOccurs uv t) =
    text "occurs check failed: the variable"
    <+> pp uv <+> "occurs in" <+> pp t
  pp (Unsimplifiable (SimplificationFail t1 t2)) =
    "failed to simplify unification problem "
    <+> pp t1 <+> nesting ("≟" <+> pp t2)

-- onUnicode' :: String -> String -> PM Doc
-- onUnicode' yes no = onUnicode (text yes) (text no)

onUnicode :: PM a -> PM a -> PM a
onUnicode yes no = do
  inUnicode <- view pcUnicode
  if inUnicode then yes else no

infixOp :: Precedence -- ^ precedence of the operator
           -> PM Doc -- ^ operator as unicode
           -> PM Doc -- ^ operator as ascii
           -> Associativity -- ^ operator associativity
           -> PM Doc -- ^ lhs pretty printer
           -> PM Doc -- ^ rhs pretty printer
           -> PM Doc
infixOp precOp opUni opAscii assoc lhs rhs =
  precParens precOp $ fsep [ withPrec precOp assoc (Left lhs),
                             onUnicode opUni opAscii,
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

(<+>) :: PM Doc -> PM Doc -> PM Doc
d1 <+> d2 = (PP.<+>) <$> d1 <*> d2

parens :: PM Doc -> PM Doc
parens = fmap PP.parens
  
text :: String -> PM Doc
text = pure . PP.text

int :: Int -> PM Doc
int = pure . PP.int

integer :: Integer -> PM Doc
integer = pure . PP.integer

fsep :: [PM Doc] -> PM Doc
fsep ds = PP.fsep <$> sequenceA ds

cat :: [PM Doc] -> PM Doc
cat ds = PP.cat <$> sequenceA ds

nesting :: PM Doc -> PM Doc
nesting = fmap (PP.nest nestingLevel)
  where
    nestingLevel = 2
