{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module FOmega.Parse where

import Data.Monoid (Monoid(..))
import Control.Applicative 
import Data.Text (Text)

import qualified Unbound.Generics.LocallyNameless as U

import Text.Parsec hiding ((<|>), many)
import Text.Parsec.Expr (Assoc(..), Operator(..), buildExpressionParser)
import Text.Parsec.Text hiding (Parser)
import qualified Text.Parsec.Token as Tok
import Text.Parsec.Token (GenLanguageDef(..), GenTokenParser)

import Insomnia.Common.Literal

import FOmega.Syntax

type Parser = Parsec Text ()

fomegaLang = LanguageDef {
  commentStart = "{-"
  , commentEnd = "-}"
  , commentLine = "--"
  , nestedComments = True
  , identStart = letter <|> char '_'
  , identLetter = alphaNum <|> char '_'
  , opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , reservedNames = ["forall", "exists", "∀", "∃",
                     "val", "type", "sig",
                     "data", "con",
                     "λ",
                     "⋆",
                     "pack", "as", "unpack", "in"
                    ]
  , reservedOpNames = ["\\", ":", ",", ".", "=", "*"]
  , caseSensitive = True
  }

Tok.TokenParser {braces, brackets
                   , symbol, reserved, identifier
                   , operator, reservedOp
                   , lexeme
                   , parens, whiteSpace
                   , integer, natural, float, naturalOrFloat
                   , comma, colon, dot
                   , commaSep, semiSep
                   } = Tok.makeTokenParser fomegaLang


fieldName :: Parser Field
fieldName =
  (FVal <$ reserved "val")
  <|> (FType <$ reserved "type")
  <|> (FSig <$ reserved "sig")
  <|> (FData <$ reserved "data")
  <|> (FCon <$ reserved "con")
  <|> (FUser <$> identifier)

kindExpr :: Parser Kind
kindExpr = buildExpressionParser table kindFactor
  where
    kindFactor = parens kindExpr
                 <|> pure KType <* starKW
    table =
      [
        [Infix arrK AssocRight]
      ]

    arrK = pure KArr <* arrowKW

    starKW = reservedOp "*" <|> reservedOp "⋆"
    arrowKW = reservedOp "->" <|> reserved "→"

variableIdentifier :: Parser (U.Name a)
variableIdentifier = U.s2n <$> identifier

tyvarType :: Parser Type
tyvarType = TV <$> variableIdentifier

kindedTyVar :: Parser [(TyVar, Kind)]
kindedTyVar =
  single <|> several
  where
    single = mkOne <$> variableIdentifier
             <* colon
             <*> kindExpr
    several = mconcat <$> many (parens single)
    mkOne v k = [(v, k)]

typeExpr :: Parser Type
typeExpr = buildExpressionParser table typeFactor
  where
    typeFactor = parens typeExpr
                 <|> tyvarType
                 <|> forallType
                 <|> existType
                 <|> tlamType
                 <|> recordType
    table =
      [
        [Infix (pure TApp) AssocLeft]
      , [Infix arrT AssocRight]
      ]

    arrT = pure TArr <* arrowKW

    arrowKW = reservedOp "->" <|> reserved "→"

typeQuantificationExpr :: Parser ([(TyVar, Kind)] -> Type -> Type) -> Parser Type
typeQuantificationExpr pQuant =
  pQuant
  <*> kindedTyVar
  <* dot
  <*> typeExpr

forallType :: Parser Type
forallType =
  typeQuantificationExpr (mkForalls <$ (reserved "forall" <|> reserved "∀"))
  where
    mkForalls [] t = t
    mkForalls ((v,k):vks) t =
      TForall $ U.bind (v, U.embed k)  (mkForalls vks t)

existType :: Parser Type
existType = typeQuantificationExpr (mkExists <$ (reserved "exists" <|> reserved "∃"))
  where
    mkExists [] t = t
    mkExists ((v, k):vks) t = TExist $ U.bind (v, U.embed k) (mkExists vks t)

tlamType :: Parser Type
tlamType = typeQuantificationExpr (mkTLams <$ (reserved "\\" <|> reserved "λ"))
  where
    mkTLams [] t = t
    mkTLams ((v, k):vks) t = TLam $ U.bind (v, U.embed k) (mkTLams vks t)

recordType :: Parser Type
recordType = TRecord <$> braces (commaSep typedField)
  where
    typedField = (,) <$> fieldName
                 <* colon
                 <*> typeExpr

termExpr :: Parser Term
termExpr = buildExpressionParser table termSummand
  where
    -- F [t1] . fld [t2] ...
    termSummand = mkSummand <$> termFactor <*> many trailingForm
    trailingForm = (Left <$> brackets typeExpr)
                   <|> (Right <$ dot <*> fieldName)
    -- (E) or v or \\x:t.E or /\x:t.E or {...} or E.f
    termFactor = parens termExpr
                 <|> varTerm
                 <|> litTerm
                 <|> lamOrPlamTerm
                 <|> recordTerm
                 <|> packTerm
                 <|> unpackTerm

    table =
      [
        [Infix (pure App) AssocLeft]
      ]

    mkSummand m [] = m
    mkSummand m (Left t:s) = mkSummand (PApp m t) s
    mkSummand m (Right f:s) = mkSummand (Proj m f) s

varTerm :: Parser Term
varTerm = V <$> variableIdentifier

litTerm :: Parser Term
litTerm = L <$> literal
  where
    literal = toLiteral <$> naturalOrFloat
    toLiteral (Right d) = RealL d
    toLiteral (Left i) = IntL i

-- λ (x1:t1) [a1:k1] ... (xN:tN) . e
lamOrPlamTerm :: Parser Term
lamOrPlamTerm =
  makeLambdas
  <$ (reservedOp "\\" <|> reserved "λ")
  <*> some abstraction
  <* dot
  <*> termExpr
  where
    -- (v : t) or [a : k]
    abstraction = (Left <$> parens ((,) <$> variableIdentifier
                                    <* colon <*> typeExpr))
                  <|> (Right <$> brackets ((,) <$> variableIdentifier
                                           <* colon <*> kindExpr))
    makeLambdas [] e = e
    makeLambdas (Left (v,t):abss) e =
      Lam $ U.bind (v, U.embed t) $ makeLambdas abss e
    makeLambdas (Right (tv, k):abss) e =
      PLam $ U.bind (tv, U.embed k) $ makeLambdas abss e
                   
recordTerm :: Parser Term
recordTerm = Record <$> braces (commaSep fieldAssn)
  where
    fieldAssn = (,)
                <$> fieldName
                <* reservedOp "="
                <*> termExpr

-- pack t , e as a:k . t
-- TODO: pack t1, t2, ... tN, e as a1:k1, ... , aN : kN . t
packTerm :: Parser Term
packTerm =
  Pack <$ reserved "pack"
  <*> typeExpr
  <* comma
  <*> termExpr
  <* reserved "as"
  <*> existPack
  where
    existPack = mkExistPack <$> variableIdentifier
                <* colon
                <*> kindExpr
                <* dot
                <*> typeExpr
    mkExistPack v k t = U.bind (v, U.embed k) t

-- unpack a,x = e in e
unpackTerm :: Parser Term
unpackTerm =
  mkUnpack <$ reserved "unpack"
  <*> variableIdentifier
  <* comma
  <*> variableIdentifier
  <* reservedOp "="
  <*> termExpr
  <* reserved "in"
  <*> termExpr
  where
    mkUnpack tv xv epack ebody =
      Unpack $ U.bind (tv, xv, U.embed epack) ebody
