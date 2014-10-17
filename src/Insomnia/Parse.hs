{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Insomnia.Parse where

import Control.Applicative
import Control.Monad (guard)
import Data.Functor.Identity
import Data.Char (isUpper, isLower)
import Data.Monoid (Monoid(..), (<>), Endo(..))
import Data.Text (Text)
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

import Insomnia.Identifier
import Insomnia.Types
import Insomnia.Expr
import Insomnia.TypeDefn
import Insomnia.ModelType
import Insomnia.Model
import Insomnia.Toplevel
import qualified Unbound.Generics.LocallyNameless as U

import Data.Format (Format(..), WrapShow(..))

newtype FormatParseError = FormatParseError ParseError

instance Format FormatParseError where
  format (FormatParseError pe) = format (WrapShow pe)

insomniaLang :: GenLanguageDef Text () Identity
insomniaLang = LanguageDef {
  commentStart = "{-"
  , commentEnd = "-}"
  , commentLine = "--"
  , nestedComments = True
  , identStart = letter <|> char '_'
  , identLetter = alphaNum <|> char '_'
  , opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , reservedNames = ["model",
                     "forall", "∀",
                     "→", "⋆", "∷",
                     "data","type", "enum", "record",
                     "val", "fun", "sig",
                     "let", "in", "case", "of",
                     "λ", "_"
                     ]
  , reservedOpNames = ["\\", "::", ".", "~", "=", "->", "*", "|"]
  , caseSensitive = True
  }

Tok.TokenParser {..} = Tok.makeTokenParser insomniaLang

coloncolon :: Parser ()
coloncolon = reservedOp "::" <|> reserved "∷"

varId :: Parser Var
varId = U.s2n <$> variableIdentifier

conId :: Parser Con
conId = Con <$> tyconIdentifier

tvarId :: Parser TyVar
tvarId = U.s2n <$> variableIdentifier

toplevel :: Parser Toplevel
toplevel = Toplevel <$> (whiteSpace *> many toplevelItem <* eof)

toplevelItem :: Parser ToplevelItem
toplevelItem = 
  (modelTypeExpr <?> "model type definition")
  <|> (modelExpr <?> "model definition")

modelExpr :: Parser ToplevelItem
modelExpr = mkModel
             <$> (try (reserved "model" *> modelId))
             <*> optional (coloncolon *> identifier)
             <*> braces (many decl)
  where
    mkModel modelName _modelSigName decls =
      ToplevelModel modelName (ModelStruct $ Model decls)

modelTypeExpr :: Parser ToplevelItem
modelTypeExpr = mkModelType
                <$> (try (reserved "model" *> reserved "type" *> modelSigId))
                <*> braces signature
  where
    mkModelType modelSigName sig =
      ToplevelModelType modelSigName (SigMT sig)

modelIdentifier :: Parser String
modelIdentifier = try $ do
  i <- identifier
  let c = head i
  guard (isUpper c)
  return i

modelId :: Parser Identifier
modelId = U.s2n <$> modelIdentifier

modelSigId :: Parser Identifier
modelSigId = U.s2n <$> modelIdentifier

signature :: Parser Signature
signature =
  makeSignature <$> (many specification)
  where
    makeSignature :: [Endo Signature] -> Signature
    makeSignature specs = appEndo (mconcat specs) UnitSig

    specification :: Parser (Endo Signature)
    specification =
      (valueSig <$> (reserved "sig" *> varId <* coloncolon)
       <*> typeExpr)

    valueSig :: Var -> Type -> Endo Signature
    valueSig v t = Endo $ \rest ->
      ValueSig (U.name2String v) (U.bind (v, U.embed t) rest)

decl :: Parser Decl
decl = (valueDecl <?> "value declaration")
       <|> (typeDecl <?> "type declaration")

valueDecl :: Parser Decl
valueDecl =
  ValueDecl <$> ((funDecl <?> "function definition")
                 <|> (sigDecl <?> "function signature")
                 <|> (valOrSampleDecl <?> "defined or sampled value"))

typeDecl :: Parser Decl
typeDecl =
  TypeDefn <$> ((dataDefn <?> "algebraic data type definition")
                <|> (enumDecl <?> "enumeration declaration"))

valOrSampleDecl :: Parser ValueDecl
valOrSampleDecl =
  mkValOrSampleDecl
  <$> (reserved "val" *> varId)
  <*> ((pure ValDecl <* reservedOp "=")
       <|> (pure SampleDecl <* reservedOp "~"))
  <*> expr
  where
    mkValOrSampleDecl v maker e = maker v e

funDecl :: Parser ValueDecl
funDecl = mkFunDecl
          <$> (reserved "fun" *> varId)
          <*> (some annVar)
          <*> (reservedOp "=" *> expr)
  where
    mkFunDecl f xs e = FunDecl f (mkLams xs e)

sigDecl :: Parser ValueDecl
sigDecl = mkSigDecl
          <$> (reserved "sig" *> varId <* coloncolon)
          <*> typeExpr
  where
    mkSigDecl f ty = SigDecl f ty

dataDefn :: Parser TypeDefn
dataDefn = mkDataDefn
           <$> (reserved "data" *> conId)
           <*> many (kindedTVar)
           <*> (reservedOp "="
                *> sepBy1 constructorDef (reservedOp "|"))
  where
    mkDataDefn nm tyvars cons =
      DataDefn nm (U.bind tyvars cons)

enumDecl :: Parser TypeDefn
enumDecl = mkEnumDefn
           <$> (reserved "enum" *> conId)
           <*> natural
  where
    mkEnumDefn = EnumDefn

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
         <|> (caseExpr <?> "case expression")

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
literal = RealL <$> try float
          <|> IntL <$> try integer
          <?> "literal double or integer"

letExpr :: Parser Expr
letExpr = mkLet
          <$> (reserved "let" *> braces bindings)
          <*> (reserved "in"  *> expr)
          <?> "let expression"
  where
    mkLet bs body = Let (U.bind bs body)

caseExpr :: Parser Expr
caseExpr = mkCase
           <$> (reserved "case" *> expr)
           <*> (reserved "of" *> braces (semiSep clause))
  where
    mkCase = Case

clause :: Parser Clause
clause = (mkClause
          <$> pattern
          <*> (reservedOp "->" *> expr))
         <?> "case expression clause"
  where
    mkClause p e = Clause (U.bind p e)

pattern :: Parser Pattern
pattern =
  atomicPattern
  <|> (valueConstructorPattern <?> "constructor pattern")

atomicPattern :: Parser Pattern
atomicPattern =
  (wildcardPattern <?> "wildcard pattern")
  <|> (variablePattern <?> "variable pattern")
  <|> parens pattern

wildcardPattern :: Parser Pattern
wildcardPattern = reserved "_" *> pure WildcardP

variablePattern :: Parser Pattern
variablePattern = VarP <$> varId

valueConstructorPattern :: Parser Pattern
valueConstructorPattern =
  ConP
  <$> conId
  <*> many atomicPattern


  
bindings :: Parser Bindings
bindings =
  mkBindings <$> semiSep binding
  where
    mkBindings [] = NilBs
    mkBindings (b:bs) =
      ConsBs $ U.rebind b (mkBindings bs)
      
binding :: Parser Binding
binding = (tabulatedFunB <?> "tabulated function definition")
          <|> (simpleBinding <?> "var = expr or var ~ expr")

simpleBinding :: Parser Binding
simpleBinding = mkBinding
          <$> annVar
          <*> bindingOperator
          <*> expr
  where
    bindingOperator = (pure SampleB <* reservedOp "~")
                      <|> (pure ValB <* reservedOp "=")
    mkBinding v op e = op v (U.embed e)

tabulatedFunB :: Parser Binding
tabulatedFunB =
  reserved "forall"
  *> (mkTabB
      <$> some annVar
      <* reserved "in"
      <*> varId
      <*> some tabSelector
      <* reservedOp "~"
      <*> expr)
  where
    mkTabB avs y sels e =
      TabB y (U.Embed
              $ TabulatedFun
              $ U.bind avs
              $ TabSample sels e)

tabSelector :: Parser TabSelector
tabSelector = (TabIndex <$> varId)

unimplemented :: String -> Parser a
unimplemented str = fail str

test :: String -> IO ()
test = parseTest expr . T.pack

testType :: String -> IO ()
testType = parseTest typeExpr . T.pack

parseFile :: FilePath -> IO (Either FormatParseError Toplevel)
parseFile fp = do
  txt <- T.readFile fp
  return (either (Left . FormatParseError) Right $ parse toplevel fp txt)
