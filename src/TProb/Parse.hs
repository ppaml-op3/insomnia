{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module TProb.Parse where

import Control.Applicative
import Control.Monad (guard)
import Data.Functor.Identity
import Data.Char (isUpper, isLower)
import Data.Text (Text)
import Data.String (IsString(..))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Text.Parsec.Text
import qualified  Text.Parsec.Token as Tok
import Text.Parsec.Token (GenLanguageDef(..))
import Text.Parsec.Char (oneOf, char, letter, alphaNum)
import Text.Parsec.Error (ParseError)
import Text.Parsec.Prim ((<?>), try, parse, parseTest)
import Text.Parsec.Combinator (eof, sepBy1)
import Text.Parsec.Expr

import TProb.Types
import TProb.AST
import qualified Unbound.Generics.LocallyNameless as U

import Data.Format (Format)

-- orphan
instance Format ParseError

tprobLang :: GenLanguageDef Text () Identity
tprobLang = LanguageDef {
  commentStart = "{-"
  , commentEnd = "-}"
  , commentLine = "--"
  , nestedComments = True
  , identStart = letter <|> char '_'
  , identLetter = alphaNum <|> char '_'
  , opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , reservedNames = ["forall", "∀",
                     "→", "⋆", "∷",
                     "data", "fun", "sig",
                     "let", "in", "case", "of",
                     "λ"
                     ]
  , reservedOpNames = ["\\", "::", ".", "~", "=", "->", "*", "|"]
  , caseSensitive = True
  }

Tok.TokenParser {..} = Tok.makeTokenParser tprobLang

coloncolon :: Parser ()
coloncolon = reservedOp "::" <|> reserved "∷"

varId :: Parser Var
varId = U.s2n <$> variableIdentifier

conId :: Parser Con
conId = Con <$> tyconIdentifier

tvarId :: Parser TyVar
tvarId = U.s2n <$> variableIdentifier

toplevel :: Parser Module
toplevel = whiteSpace *> moduleExpr <* eof

moduleExpr :: Parser Module
moduleExpr = Module <$> many decl

decl :: Parser Decl
decl = (funDecl <?> "function definition")
       <|> (sigDecl <?> "function signature")
       <|> (dataDecl <?> "datatype definition")

funDecl :: Parser Decl
funDecl = mkFunDecl
          <$> (reserved "fun" *> varId)
          <*> (some annVar)
          <*> (reservedOp "=" *> expr)
  where
    mkFunDecl f xs e = FunDecl f (mkLams xs e)

sigDecl :: Parser Decl
sigDecl = mkSigDecl
          <$> (reserved "sig" *> varId <* coloncolon)
          <*> typeExpr
  where
    mkSigDecl f ty = SigDecl f ty

dataDecl :: Parser Decl
dataDecl = mkDataDecl
           <$> (reserved "data" *> conId)
           <*> some (kindedTVar)
           <*> (reservedOp "="
                *> sepBy1 constructorDef (reservedOp "|"))
  where
    mkDataDecl nm tyvars cons =
      DataDecl nm (U.bind tyvars cons)

kindedTVar :: Parser (TyVar, Kind)
kindedTVar =
  parens ((,) <$> tvarId
          <*> (coloncolon *> kindExpr))

constructorDef :: Parser ConstructorDef
constructorDef =
  mkConstructorDef
  <$> conId
  <*> many atomicTy
  where
    mkConstructorDef c tys = ConstructorDef c tys

typeExpr :: Parser Type
typeExpr =
  mkArr <$> sepBy1 juxtaposeTy tyarrowKW
  where
    tyarrowKW = reservedOp "->" <|> reserved "→"

    mkArr [] = error "unexpected empty"
    mkArr [ty] = ty
    mkArr (ty1:tys) = TApp (TApp tarrow ty1) (mkArr tys)

    tarrow = TC (Con "->")

juxtaposeTy :: Parser Type
juxtaposeTy = mkApp <$> some atomicTy
  where
    mkApp [] = error "can't happen"
    mkApp (f:es) = mkApp' f es

    mkApp' f [] = f
    mkApp' f (e:es) = mkApp' (TApp f e) es

atomicTy :: Parser Type
atomicTy =   tcon
  <|> tvar
  <|> tforall
  <|> parens typeExpr

tcon :: Parser Type
tcon = TC <$> conId

tvar :: Parser Type
tvar = TV <$> tvarId

tforall :: Parser Type
tforall = mkForall
          <$> (forallKW *> some (parens varColonColonKind))
          <*> (reservedOp "." *> typeExpr)
  where
    mkForall [] ty = ty
    mkForall ((v,k):vks) ty =
      TForall (U.bind (v, k) (mkForall vks ty))

    varColonColonKind = (,) <$> tvarId
                        <*> (coloncolon *> kindExpr)

    forallKW = reserved "forall" <|> reserved "∀"

kindExpr :: Parser Kind
kindExpr = buildExpressionParser table kindFactor
  where
    kindFactor = parens kindExpr
                 <|> pure KType <* starKW

    table =
      [
        [Infix arrK AssocRight]
      ]

    arrK = arrowKW *> pure KArr
    
    starKW = reservedOp "*" <|> reservedOp "⋆"
    arrowKW = reservedOp "->" <|> reserved "→"

expr :: Parser Expr
expr = maybeAnn
       <$> (mkApp <$> some factor)
       <*> optional (coloncolon *> typeExpr)
  where
    mkApp [] = error "can't happen"
    mkApp (f:es) = mkApp' f es

    mkApp' f [] = f
    mkApp' f (e:es) = mkApp' (App f e) es

    maybeAnn f (Just ty) = Ann f ty
    maybeAnn f Nothing = f

factor :: Parser Expr
factor = (lam <?> "lambda expression")
         <|> (var <?> "variable")
         <|> (con <?> "type constructor")
         <|> (lit <?> "literal")
         <|> (parens expr <?> "parenthesized expression")
         <|> (letExpr <?> "let expression")

lam :: Parser Expr
lam = mkLams <$> (lambdaKW *> some annVar)
       <*> (dot *> expr)
  where        
    lambdaKW = reservedOp "\\" <|> reserved "λ"

-- | Make a sequence of nested lambdas
mkLams :: [(Var, U.Embed Annot)] -> Expr -> Expr
mkLams [] _ = error "cannot have lambda with no variables"
mkLams [v] e = Lam (U.bind v e)
mkLams (v:vs) e = Lam (U.bind v (mkLams vs e))

annVar :: Parser (Var, U.Embed Annot)
annVar = (unannotated <$> varId)
         <|> parens (annotated
                     <$> varId
                     <*> (coloncolon *> typeExpr))
         <?> "var or (var :: ty)"
  where
    unannotated v = (v, U.embed $ Annot Nothing)
    annotated v ty = (v, U.embed . Annot $ Just ty)



variableIdentifier :: Parser String
variableIdentifier = try $ do
  i <- identifier
  let c = head i
  guard (isLower c || c == '_')
  return i
  

tyconIdentifier :: Parser String
tyconIdentifier = try $ do
  i <- identifier
  let c = head i
  guard (isUpper c)
  return i

var :: Parser Expr
var = V <$> varId <?> "variable"

con :: Parser Expr
con = C <$> conId <?> "type constructor"

lit :: Parser Expr
lit = L <$> literal

literal :: Parser Literal
literal = DoubleL <$> try float
          <|> IntL <$> try integer
          <?> "literal double or integer"

letExpr :: Parser Expr
letExpr = mkLet
          <$> (reserved "let" *> braces (semiSep1 binding))
          <*> (reserved "in"  *> expr)
          <?> "let expression"
  where
    mkLet bs body = Let (U.bind bs body)

binding :: Parser Binding
binding = mkBinding
          <$> annVar
          <*> bindingOperator
          <*> expr
  where
    bindingOperator = (pure SampleB <* reservedOp "~")
                      <|> (pure LetB <* reservedOp "=")
    mkBinding v op e = op v (U.embed e)

unimplemented :: String -> Parser a
unimplemented str = fail str

test :: String -> IO ()
test = parseTest expr . T.pack

testType :: String -> IO ()
testType = parseTest typeExpr . T.pack

parseFile :: FilePath -> IO (Either ParseError Module)
parseFile fp = do
  txt <- T.readFile fp
  return (parse toplevel fp txt)
