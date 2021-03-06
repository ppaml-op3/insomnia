{-# LANGUAGE RecordWildCards, OverloadedStrings, NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Insomnia.SurfaceSyntax.Parse (parseHandle, parseText, bigExpr, toplevel) where

import Control.Applicative
import Control.Monad (guard)
import Control.Lens (set, over)

import Data.Char (isUpper, isLower)
import Data.List (isPrefixOf)
import Data.Functor.Identity (Identity(..))
import Data.Text (Text)
import qualified Data.Text.IO as T
import Data.Ratio ((%))

import System.IO (Handle)
import Text.Parsec.Char (char, letter, alphaNum, oneOf, noneOf)
import Text.Parsec.Combinator (eof, sepBy1, between, many1, manyTill, chainl1)
import Text.Parsec.Error (ParseError)
import qualified Text.Parsec.Token as Tok hiding (makeTokenParser)
import qualified Text.Parsec.Indentation.Token as Tok
import Text.Parsec.Token (GenLanguageDef(..))
import Text.Parsec.Prim (Parsec, (<?>), try, parse)
import Text.Parsec.Expr (Operator(..), buildExpressionParser)
import Text.Parsec.Indentation (IndentStream, mkIndentStream,
                                IndentationRel(..), localTokenMode, absoluteIndentation,
                                localIndentation,
                                infIndentation)
import Text.Parsec.Indentation.Char (CharIndentStream, mkCharIndentStream)
import Text.Parsec.Text () -- parsec < 3.1.7 Text Stream instances are here.

import Data.Format (Format(..), WrapShow(..))

import Insomnia.Common.Literal
import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Common.SampleParameters
import Insomnia.SurfaceSyntax.Syntax
import Insomnia.SurfaceSyntax.SourcePos (Positioned(..), positioned, parsePositioned)
import Insomnia.SurfaceSyntax.FixityParser (Fixity(..), Assoc(..))

newtype FormatParseError = FormatParseError ParseError

instance Format FormatParseError where
  format (FormatParseError pe) = format (WrapShow pe)

--

type InsomniaStream = IndentStream (CharIndentStream Text)

type Parser = Parsec InsomniaStream () 

----------------------------------------

insomniaLang :: GenLanguageDef InsomniaStream () Identity
insomniaLang = Tok.makeIndentLanguageDef $ LanguageDef {
  commentStart = "{-"
  , commentEnd = "-}"
  , commentLine = "--"
  , nestedComments = True
  , identStart = letter <|> char '_'
  , identLetter = alphaNum <|> char '_'
  , opStart = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , reservedNames = ["model", "module", "local",
                     "import", "using",
                     "observe", "is",
                     "unpack", "as",
                     "pack",
                     "query",
                     "where",
                     "forall", "∀",
                     "⋆", "∷", "→",
                     "infix", "infixr", "infixl",
                     "assume",
                     "data", "type", "enum",
                     "parameter", "random",
                     "val", "fun", "sig",
                     "let", "in", "case", "of",
                     "return",
                     "λ", "_"
                     ]
  , reservedOpNames = ["\\", ":", ".", "~", "=", "*", "|", "{{", "}}"]
  , caseSensitive = True
  }

Tok.TokenParser {braces = _
                , symbol, reserved, identifier
                , operator, reservedOp
                , lexeme
                , parens, whiteSpace
                , integer, natural, float
                , commaSep, semiSep
                } = Tok.makeTokenParser insomniaLang

-- For braces, the leading brace opens a scope where the next production can be in any column, and
-- the closing brace likewise.
-- For example:
--     foo = {
--  stuff
--     }
-- 
braces = between (localIndentation Any $ symbol "{") (localIndentation Any $ symbol "}") . localIndentation Any

dblbraces =
  between (localIndentation Any $ try (symbol "{{")) (localIndentation Any $ try (symbol "}}"))

exactly :: (Show a, Eq a) => Parser a -> a -> Parser ()
exactly p x = (p >>= \x' -> guard (x == x')) <?> show x

quotedLiteralString :: Parser String
quotedLiteralString =
  let quo = char '"'
      stringChar = noneOf "\"\t\n\r" <?> "string characters"
  in lexeme (do
                _ <- quo
                manyTill stringChar (try quo)) <?> "double quoted string"

----------------------------------------

classify :: Parser ()
classify = reservedOp ":" -- reservedOp "::" <|> reserved "∷"

variableIdentifier :: Parser Ident
variableIdentifier = try $ do
  i <- identifier
  let c = head i
  guard (isLower c || c == '_')
  return i

variableOrPrefixInfixIdentifier :: Parser Ident
variableOrPrefixInfixIdentifier =
  try (parens operator)
  <|> variableIdentifier

modelIdentifier :: Parser Ident
modelIdentifier = tyconIdentifier

moduleTypeIdentifier :: Parser Ident
moduleTypeIdentifier = tyconIdentifier

tyconIdentifier :: Parser Ident
tyconIdentifier = (try $ do
  i <- identifier
  let c = head i
  guard (isUpper c || "__" `isPrefixOf` i)
  return i) <?> "type identifier"

infixIdent :: Parser Ident
infixIdent = operator

-- | @qualifiedName p@ is a parser that parses
-- a sequence of Initial-uppercase identifiers separated by "." with no
-- intervening whitespace followed by @p@.  For example "X.Y.Z.<p>"
qualifiedName :: Parser a -> Parser ([String], a)
qualifiedName p =
  let components = do
        c <- (Left <$> try (component <* char '.'))
             <|> (Right <$> p)
        case c of
          Left s -> do 
            (ss, x) <- components
            return (s:ss, x)
          Right x -> return ([], x)
      upComponent = do
        c <- identStart insomniaLang
        guard (isUpper c)
        cs <- many (identLetter insomniaLang)
        return (c:cs)
      doubleUnderComponent = do
        _ <- try (char '_')
        _ <- char '_'
        cs <- many (identLetter insomniaLang)
        return ("__"++cs)
      component =
        (doubleUnderComponent <|> upComponent) <?> "module path component"
  in lexeme $ components

qualifiedInfixIdent :: Parser QualifiedIdent
qualifiedInfixIdent =
  (mkQualifiedIdent <$> qualifiedName infixIdent)
  <?> "(possibly qualified) infix identifier"
  where
    mkQualifiedIdent (path, ident) = QId path ident

-- | X.Y.<op> where <op> is a symbolic operator
infixConId :: Parser Con
infixConId =
  Con <$> qualifiedInfixIdent

-- | X.Y.Z -- all components initial-uppercase
conId :: Parser Con
conId = ((Con . mkQId) <$> qualifiedName tyconIdentifier)
        <?> "(possibly qualified) constructor identifier"
  where
    mkQId (path,ident) = QId path ident


-- | X.Y.Z.v -- all components except the last are initial-uppsercase
qvarId :: Parser Var
qvarId = ((Var . mkQId) <$> qualifiedName variableIdentifier)
         <?> "possibly qualified value identifier"
  where
    mkQId (path,ident) = QId path ident

tvarId :: Parser TyVar
tvarId = TyVar <$> variableIdentifier

modelId :: Parser QualifiedIdent
modelId = (mkQId <$> qualifiedName modelIdentifier)
          <?> "possibly qualified module identifier"
  where mkQId = uncurry QId

----------------------------------------
    
parseHandle :: FilePath -> Handle -> IO (Either FormatParseError Toplevel)
parseHandle fp h =
  parseText fp toplevel <$> T.hGetContents h

parseText :: FilePath -> Parser a -> Text -> Either FormatParseError a
parseText fp p txt =
  let s = mkIndentStream 0 infIndentation True Gt $ mkCharIndentStream txt
  in either (Left . FormatParseError) Right $ parse p fp s
----------------------------------------

toplevel :: Parser Toplevel
toplevel = Toplevel
           <$ whiteSpace
           <*> (localIndentation Any $ many $ absoluteIndentation toplevelItem)
           <* finish
  where
    finish = localTokenMode (const Any) eof

toplevelItem :: Parser ToplevelItem
toplevelItem =
  (toplevelBigExpr <?> "toplevel module, model, module type or model type declaration")
  <|> (toplevelQuery <?> "toplevel query expression")
  <|> (toplevelImport <?> "toplevel import declaration")

toplevelBigExpr :: Parser ToplevelItem
toplevelBigExpr = parsePositioned toplevelBigExpr_

toplevelBigExpr_ :: Parser ToplevelItem_
toplevelBigExpr_ =
  mkToplevelBigExpr <$> tyconIdentifier
  <*> optional (parsePositioned (classify *> bigExpr))
  <* reservedOp "="
  <*> bigExpr
  where
    mkToplevelBigExpr ident Nothing be = ToplevelBigExpr ident be
    mkToplevelBigExpr ident (Just psigBE) be =
      ToplevelBigExpr ident (over positioned (SealBE be) psigBE)

bigExpr :: Parser BigExpr
bigExpr =
  factorBigExpr `chainl1` (mkSealBE <$> parsePositioned classify) -- (M : S) : S'
  where
    mkSealBE :: Positioned a -> BigExpr -> BigExpr -> BigExpr
    mkSealBE pseal m s = set positioned (SealBE m s) pseal

factorBigExpr :: Parser BigExpr
factorBigExpr =
  whereTypeBE <$> atomicBigExpr
  <*> many (parsePositioned whereTypeClause)
  where
    -- BigExpr -> [Positioned WhereClause] -> BigExpr
    whereTypeBE = foldl mkWhereTypeBE
    mkWhereTypeBE be pwh = over positioned (WhereTypeBE be) pwh

atomicBigExpr :: Parser BigExpr
atomicBigExpr =
  (abstractionBigExpr <?> "functor or functor signature")
  <|> (assumeBigExpr <?> "assumed module")
  <|> (classifierBigExpr <?> "literal model type or module type signature")
  <|> (literalBigExpr <?> "literal model or module structure")
  <|> (applicationOrVarBigExpr <?> "functor application")
  <|> (localBigExpr <?> "model local declaration")
  <|> (observeBigExpr <?> "model observation")
  <|> (unpackBigExpr <?> "first class module unpacking")
  <|> parens bigExpr

classifierBigExpr :: Parser BigExpr
classifierBigExpr =
  parsePositioned (ClassifierBE <$> try (moduleKind <* reserved "type")
                   <*> braces signature)

literalBigExpr :: Parser BigExpr
literalBigExpr =
  parsePositioned (LiteralBE <$> moduleKind
                   <*> moduleLiteral)

assumeBigExpr :: Parser BigExpr
assumeBigExpr =
  parsePositioned (AssumeBE <$ reserved "assume"
                   <*> atomicBigExpr)

applicationOrVarBigExpr :: Parser BigExpr
applicationOrVarBigExpr =
  parsePositioned (mkAppBE <$> modulePath
                   <*> optional (parens $ commaSep modulePath))
  where
    modulePath = modelId
    mkAppBE p Nothing = VarBE p
    mkAppBE p (Just args) = AppBE p args

abstractionBigExpr :: Parser BigExpr
abstractionBigExpr =
  parsePositioned (AbsBE <$> try (functorArguments <* arrowKW)
                   <*> bigExpr)
  where
    arrowKW = reservedOp "->" <|> reserved "→"

localBigExpr :: Parser BigExpr
localBigExpr =
  parsePositioned (LocalBE <$ reserved "local"
                   <*> (Module <$> declList)
                   <* reserved "in"
                   <*> atomicBigExpr
                   <* classify
                   <*> bigExpr)

observeBigExpr :: Parser BigExpr
observeBigExpr =
  parsePositioned (ObserveBE <$ reserved "observe"
                   <*> atomicBigExpr
                   <*> many1 observationClause)

unpackBigExpr :: Parser BigExpr
unpackBigExpr =
  parsePositioned (UnpackBE <$ reserved "unpack"
                   <*> dblbraces expr
                   <* reserved "as"
                   <*> atomicBigExpr)


moduleKind :: Parser ModuleKind
moduleKind =
  ((ModelMK <$ reserved "model")
   <|> (ModuleMK <$ reserved "module"))
  <?> "module kind"

toplevelQuery :: Parser ToplevelItem
toplevelQuery = parsePositioned toplevelQuery_

toplevelQuery_ :: Parser ToplevelItem_
toplevelQuery_ =
  ToplevelQuery <$ reserved "query" <*> queryExpr

toplevelImport :: Parser ToplevelItem
toplevelImport = parsePositioned toplevelImport_

toplevelImport_ :: Parser ToplevelItem_
toplevelImport_ =
  ToplevelImport <$ reserved "import"
  <*> importFileSpec
  <*> parens (localIndentation Any $ many $ absoluteIndentation importSpecItem)

importFileSpec :: Parser ImportFileSpec
importFileSpec = ImportFileSpec <$> quotedLiteralString

importSpecItem :: Parser ImportSpecItem
importSpecItem =
  (try (ImportModuleTypeSpecItem <$ reserved "module" <* reserved "type") <*> moduleTypeIdentifier)
  <|> (importModuleSpecItem <$ reserved "module") <*> modelIdentifier <*> optional (reserved "using" *> modelIdentifier)
  where
    importModuleSpecItem x Nothing =
      ImportModuleSpecItem x x
    importModuleSpecItem x (Just y) = ImportModuleSpecItem x y
      
queryExpr :: Parser QueryExpr
queryExpr =
  mkGenSamplesQE <$ sampleKW <*> modelId <*> natural
  where
    sampleKW = 
      (try (identifier >>= guard . (== "sample"))) <?> "sample keyword"
    mkGenSamplesQE p n =
      GenSamplesQE p (SampleParameters (fromInteger n) useDefault)

  
signature :: Parser Signature
signature =
  Sig <$> localIndentation Ge (many $ absoluteIndentation sigDecl)

sigDecl :: Parser SigDecl
sigDecl =
  (submoduleSig <?> "submodule or submodel declaration")
  <|> (valueSig <?> "value signature declaration")
  <|> (typeSig <?> "type signature or type alias definition")
  <|> (fixitySig <?> "fixity declaration")

submoduleSig :: Parser SigDecl
submoduleSig =
  SubmoduleSig
  <$> modelIdentifier
  <* classify
  <*> bigExpr

valueSig :: Parser SigDecl
valueSig =
  ValueSig
  <$> optStochasticity
  <*> (reserved "sig" *> variableOrPrefixInfixIdentifier)
  <* classify
  <*> typeExpr


optStochasticity :: Parser (Maybe Stochasticity)
optStochasticity =
  ((try (reserved "parameter") *> pure (Just DeterministicParam))
   <|> (try (reserved "random") *> pure (Just RandomVariable))
   <|> pure Nothing
  ) <?> "'parameter' or 'random' (or infer from context)"

typeSig :: Parser SigDecl
typeSig =
  mkTypeSig
  <$> ((manifestTypeSigDecl <$> (dataDefn <|> enumDefn))
       <|> abstractDeclOrAliasDefn)
  where
    mkTypeSig (ident, tySigDecl) = TypeSig ident tySigDecl

    manifestTypeSigDecl (ident, td) = (ident, ManifestTypeSigDecl td)

    abstractDeclOrAliasDefn =
      abstractOrAlias
      <$> (reserved "type" *> tyconIdentifier)
      <*> ((Left <$> (classify *> kindExpr))
           <|> (Right <$> ((,)
                           <$> many kindedTVar
                           <* reservedOp "="
                           <*> typeExpr)))

    abstractOrAlias ident (Left k) =
      (ident, AbstractTypeSigDecl k)
    abstractOrAlias ident (Right (tvks, ty)) =
      (ident, AliasTypeSigDecl (TypeAlias tvks ty))

fixitySig :: Parser SigDecl
fixitySig =
  mkFixitySig <$> fixity
  where
    mkFixitySig (ident, f) = FixitySig ident f

fixity :: Parser (Ident, Fixity)
fixity =
  mkFixity
  <$> fixityKW
  <*> operator
  <*> fixprecedence
  where
    mkFixity assc ident prec = (ident, Fixity assc prec)

    fixityKW = (reserved "infix" *> pure AssocNone)
               <|> (reserved "infixl" *> pure AssocLeft)
               <|> (reserved "infixr" *> pure AssocRight)
    fixprecedence =
      mkRational <$> integer <*> optional (exactly operator "/" *> integer)
      
    mkRational :: Integer -> Maybe Integer -> Rational
    mkRational num (Just denom) = num % denom
    mkRational num Nothing = num % 1

whereTypeClause :: Parser WhereClause
whereTypeClause =
  WhereTypeCls
  <$ reserved "where"
  <* reserved "type"
  <*> conId
  <* reservedOp "="
  <*> typeExpr

observationClause :: Parser ObservationClause
observationClause =
  ObservationClause
  <$ reserved "where"
  <*> modelIdentifier
  <* reserved "is"
  <*> atomicBigExpr

functorArguments :: Parser [(Ident, BigExpr)]
functorArguments =
  parens (commaSep namedSigComponent <?> "zero or more module/model modId : SIG elements") 
  where
    namedSigComponent = (,) <$> moduleTypeIdentifier <* classify <*> bigExpr

declList :: Parser [Decl]
declList = localIndentation Ge $ many $ absoluteIndentation decl

moduleLiteral :: Parser Module
moduleLiteral =
  Module <$> braces declList

bigSubmoduleOrSampleDefn =
  mk <$> modelIdentifier
  <*> optional (parsePositioned (classify *> bigExpr))
  <*> ((BigSubmoduleDefn <$ reservedOp "=")
       <|> (BigSampleDefn <$ reservedOp "~"))
  <*> bigExpr
  where
    mk :: Ident -> Maybe (Positioned BigExpr)
          -> (Ident -> BigExpr -> Decl) -> BigExpr -> Decl
    mk ident Nothing maker be = maker ident be
    mk ident (Just psigBE) maker be = maker ident (over positioned (SealBE be) psigBE)

decl :: Parser Decl
decl = (valueDecl <?> "value declaration")
       <|> (importDecl <?> "import declaration")
       <|> (fixityDecl <?> "fixity declaration")
       <|> (typeDefn <?> "type definition")
       <|> (typeAliasDefn <?> "type alias definition")
       <|> (bigSubmoduleOrSampleDefn <?> "submodule definiton or sample from model")
       <|> (tabulatedSampleDecl <?> "tabulated function definition")

fixityDecl :: Parser Decl
fixityDecl = uncurry FixityDecl <$> fixity

importDecl :: Parser Decl
importDecl =
  mkImportDecl
  <$ reserved "import"
  <*> modelId
  where
    mkImportDecl = ImportDecl
    
valueDecl :: Parser Decl
valueDecl =
  mkValueDecl <$> ((funDecl <?> "function definition")
                   <|> (valueSigDecl <?> "function signature")
                   <|> (valOrSampleDecl <?> "defined or sampled value")
                   <|> (parameterDecl <?> "parameter definition"))
  where
    mkValueDecl (fld, d) = ValueDecl fld d

typeDefn :: Parser Decl
typeDefn =
  mkTypeDefn <$> ((dataDefn <?> "algebraic data type definition")
                  <|> (enumDefn <?> "enumeration declaration"))
  where
    mkTypeDefn (fld, d) = TypeDefn fld d

typeAliasDefn :: Parser Decl
typeAliasDefn =
  mkTypeAliasDefn
  <$> (reserved "type" *> tyconIdentifier)
  <*> many kindedTVar
  <* reservedOp "="
  <*> typeExpr
  where
    mkTypeAliasDefn fld tyvars ty =
      TypeAliasDefn fld (TypeAlias tyvars ty)

funDecl :: Parser (Ident, ValueDecl)
funDecl =
  mkFunDecl
  <$> (reserved "fun" *> variableOrPrefixInfixIdentifier)
  <*> (some annVar)
  <*> (reservedOp "=" *> expr)
  where
    mkFunDecl f xs e = (f, FunDecl (mkLams xs e))

tabulatedSampleDecl :: Parser Decl
tabulatedSampleDecl =
  TabulatedSampleDecl <$> tabulatedDecl

-- | Make a sequence of nested lambdas
mkLams :: [(Ident, Maybe Type)] -> Expr -> Expr
mkLams [] _ = error "cannot have lambda with no variables"
mkLams [(v, mty)] e = Lam v mty e
mkLams ((v, mty):vs) e = Lam v mty (mkLams vs e)

valueSigDecl :: Parser (Ident, ValueDecl)
valueSigDecl =
  mkSigDecl
  <$> try (optStochasticity <* reserved "sig")
  <*> variableOrPrefixInfixIdentifier
  <* classify
  <*> typeExpr
  where
    mkSigDecl stoch f ty = (f, SigDecl stoch ty)

parameterDecl :: Parser (Ident, ValueDecl)
parameterDecl =
  mkParameterDecl
  <$> try (reserved "parameter" *> variableOrPrefixInfixIdentifier)
  <* reservedOp "="
  <*> expr
  where
    mkParameterDecl f e = (f, ValDecl (Just DeterministicParam) e)

valOrSampleDecl :: Parser (Ident, ValueDecl)
valOrSampleDecl =
  mkValOrSampleDecl
  <$> (reserved "val" *> variableOrPrefixInfixIdentifier)
  <*> ((pure (ValDecl Nothing) <* reservedOp "=")
       <|> (pure SampleDecl <* reservedOp "~"))
  <*> expr
  where
    mkValOrSampleDecl v maker e = (v, maker e)


dataDefn :: Parser (Ident, TypeDefn)
dataDefn = mkDataDefn
           <$> (reserved "data" *> tyconIdentifier)
           <*> many (kindedTVar)
           <*> (reservedOp "="
                *> sepBy1 constructorDef (reservedOp "|"))
  where
    mkDataDefn nm tyvars cons = (nm, DataTD $ DataDefn tyvars cons)

enumDefn :: Parser (Ident, TypeDefn)
enumDefn = mkEnumDefn
           <$> (reserved "enum" *> tyconIdentifier)
           <*> natural
  where
    mkEnumDefn nm card = (nm, EnumTD card)

constructorDef :: Parser ConstructorDef
constructorDef =
  ConstructorDef
  <$> tyconIdentifier
  <*> many (atomicTy <$> typeAtom)
  where
    atomicTy atm = TPhrase [atm]

kindedTVar :: Parser KindedTVar
kindedTVar =
  parens ((,) <$> tvarId
          <*> (classify *> kindExpr))

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

typeAtom :: Parser TypeAtom
typeAtom =
  (TV <$> tvarId)
  <|> (TC <$> try ((PrefixN <$> conId)
                   <|> (InfixN <$> infixConId)))
  <|> (TEnclosed <$> tforall <*> pure Nothing)
  <|> dblbraces (TPack <$> bigExpr)
  <|> (TRecord <$> recordRow)
  <|> parens (TEnclosed <$> typeExpr
              <*> optional (classify *> kindExpr))

recordRow :: Parser Row
recordRow =
  Row <$> (braces (semiSep labeledType))
  where
    labeledType = (,) <$> label <* classify <*> typeExpr

label :: Parser Label
label = Label <$> variableIdentifier

typeExpr :: Parser Type
typeExpr =
  TPhrase <$> many typeAtom

tforall :: Parser Type
tforall = mkForall
          <$> (forallKW *> some kindedTVar)
          <*> (reservedOp "." *> typeExpr)
  where
    mkForall [] ty = ty
    mkForall ((v,k):vks) ty =
      TForall v k (mkForall vks ty)

    forallKW = reserved "forall" <|> reserved "∀"

annVar :: Parser (Ident, Maybe Type)
annVar = (unannotated <$> variableIdentifier)
         <|> parens (annotated
                     <$> variableIdentifier
                     <*> (classify *> typeExpr))
         <?> "var or (var :: ty)"
  where
    unannotated v = (v, Nothing)
    annotated v ty = (v, Just ty)

expr :: Parser Expr
expr =
  (lamExpr <?> "lambda expression")
  <|> (caseExpr <?> "case expression")
  <|> (letExpr <?> "let expression")
  <|> (Phrase <$> some exprAtom)

exprNotationIdentifier :: Parser ExprAtom
exprNotationIdentifier =
  ((V . PrefixN) <$> try qvarId)
  <|> ((V . InfixN . Var) <$> try qualifiedInfixIdent)
  <|> ((C . PrefixN) <$> try conId)

exprAtom :: Parser ExprAtom
exprAtom =
  exprNotationIdentifier
  <|> (L <$> literal)
  <|> recordExpression
  <|> returnExpression
  <|> packExpression
  <|> parens (Enclosed <$> expr
              <*> optional (classify *> typeExpr))

returnExpression :: Parser ExprAtom
returnExpression =
  Return <$> (reserved "return" *> exprAtom)

packExpression :: Parser ExprAtom
packExpression =
  Pack <$ reserved "pack"
  <*> dblbraces bigExpr
  <* reserved "as"
  <*> atomicBigExpr

recordExpression :: Parser ExprAtom
recordExpression =
  Record <$> braces (commaSep labeledAssignExpr)
  where
    labeledAssignExpr = (,) <$> label <* reservedOp "=" <*> expr

literal :: Parser Literal
literal = RealL <$> try float
          <|> IntL <$> try integer
          <?> "literal double or integer"

lamExpr :: Parser Expr
lamExpr =
  mkLam <$ (reservedOp "\\" <|> reservedOp "λ")
  <*> annVar
  <* (reservedOp "->" <|> reservedOp "→")
  <*> expr
  where
    mkLam (x,mt) e = Lam x mt e

caseExpr :: Parser Expr
caseExpr = Case
           <$> (reserved "case" *> expr)
           <*> (reserved "of" *> (eClauses <|> iClauses))
  where
    -- explicit braces
    eClauses = braces (semiSep clause)
    -- implicit indentation
    iClauses = localIndentation Gt $ many $ absoluteIndentation clause
  
letExpr :: Parser Expr
letExpr = Let
          <$> (reserved "let" *> (eBindings <|> iBindings))
          <*> (reserved "in"  *> expr)
  where
    eBindings = braces (semiSep binding)
    iBindings = localIndentation Gt (many $ absoluteIndentation binding)
    
clause :: Parser Clause
clause = (Clause
          <$> simplePattern
          <*> (exactly operator "->" *> expr))
         <?> "case expression clause"
  where
    simplePattern = mkPattern <$> patternAtom
    mkPattern pa = PhraseP [pa]

patternAtom :: Parser PatternAtom
patternAtom =
  ((pure WildcardP <* reserved "_") <?> "wildcard pattern")
  <|> ((ConP <$> ((PrefixN <$> conId)
                  <|> (InfixN . Con <$> qualifiedInfixIdent)))
       <?> "constructor pattern")
  <|> (VarP <$> variableIdentifier <?> "variable pattern")
  <|> recordPattern
  <|> parens (EnclosedP <$> pattern)

recordPattern :: Parser PatternAtom
recordPattern =
  RecordP <$> braces (commaSep labeledPattern)
  where
    labeledPattern = (,) <$> label <* reservedOp "=" <*> pattern

pattern :: Parser Pattern
pattern = PhraseP <$> some patternAtom

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
    mkBinding (v, mty) op e = op v (Phrase [Enclosed e mty])

tabulatedFunB :: Parser Binding
tabulatedFunB = TabB <$> tabulatedDecl

tabulatedDecl :: Parser TabulatedDecl
tabulatedDecl =
  mkTabDecl
  <$ reserved "forall"
  <*> some annVar
  <* reserved "in"
  <*> some tabs
  where
    tabs =
      mkTabulatedFun
      <$> variableIdentifier
      <*> some tabSelector
      <* reservedOp "~"
      <*> expr
    mkTabulatedFun y sels e =
      TabulatedFun y $ TabSample sels e
    mkTabDecl avs tfs =
      TabulatedDecl avs tfs

tabSelector :: Parser TabSelector
tabSelector = (TabIndex <$> variableIdentifier)
