module Insomnia.SurfaceSyntax.Syntax where

import Data.Monoid ((<>))

import Insomnia.SurfaceSyntax.FixityParser (Fixity)

type Ident = String

type Nat = Integer

data QualifiedIdent = QId ![Ident] !Ident
                    deriving (Show)

instance Ord QualifiedIdent where
  (QId p1 f1) `compare` (QId p2 f2) = compare p1 p2 <> compare f1 f2

instance Eq QualifiedIdent where
  q1 == q2 = compare q1 q2 == EQ

data Toplevel = Toplevel ![ToplevelItem]
              deriving (Show)

data ToplevelItem =
  ToplevelModel !Ident !(Maybe ModelType) !ModelExpr
  | ToplevelModelType !Ident ModelType
    deriving (Show)

data ModelExpr =
  ModelStruct !Model
  | ModelAscribe !ModelExpr !ModelType
  | ModelAssume !ModelType
  | ModelId !QualifiedIdent
    deriving (Show)
             
data ModelType =
  SigMT !Signature
  | IdentMT !Ident
    deriving (Show)

data Signature = Sig ![SigDecl]
               deriving (Show)

data SigDecl = ValueSig !Ident !Type
             | FixitySig !Ident !Fixity
             | TypeSig !Ident !TypeSigDecl
             | SubmodelSig !Ident !ModelType
             deriving (Show)

data TypeSigDecl =
  AbstractTypeSigDecl !Kind
  | ManifestTypeSigDecl !TypeDefn
  | AliasTypeSigDecl !TypeAlias
  deriving (Show)

data TypeDefn =
  DataTD !DataDefn
  | EnumTD !Nat
  deriving (Show)

type KindedTVar = (Ident,Kind)

data TypeAlias = TypeAlias ![KindedTVar] !Type
               deriving (Show)

data DataDefn = DataDefn ![KindedTVar] ![ConstructorDef]
              deriving (Show)

data ConstructorDef = ConstructorDef !Ident ![Type]
                    deriving (Show)

data Model = Model ![Decl]
           deriving (Show)

data Decl = ValueDecl !Ident !ValueDecl
          | TypeDefn !Ident !TypeDefn
          | TypeAliasDefn !Ident !TypeAlias
          | SubmodelDefn !Ident !ModelExpr
          | FixityDecl !Ident !Fixity
          deriving (Show)

data ValueDecl =
  FunDecl !Expr
  | ValDecl !Expr
  | SampleDecl !Expr
  | SigDecl !Type
  deriving (Show)

data Kind = KType | KArr !Kind !Kind
          deriving (Show)

data TypeAtom = TI !QualifiedIdent
              | TEnclosed !Type !(Maybe Kind)  -- '(' Type ')' or '(' Type ':' Kind ')'
              deriving (Show)

data Type = TPhrase ![TypeAtom]
          | TForall !Ident !Kind !Type
          deriving (Show)

data Literal = IntL !Integer
             | RealL !Double
             deriving (Show)

data ExprAtom = I !QualifiedIdent
              | L !Literal
              | Enclosed !Expr !(Maybe Type) -- '(' Expr ')' or '(' Expr ':' Type ')'
              deriving (Show)

data Expr = Phrase ![ExprAtom]
          | Lam !Ident !(Maybe Type) !Expr
          | Case !Expr ![Clause]
          | Let ![Binding] !Expr
          deriving (Show)

data Clause = Clause !Pattern !Expr
            deriving (Show)

data PatternAtom = WildcardP
                 | IdP !QualifiedIdent
                 | EnclosedP !Pattern
                  deriving (Show)

data Pattern = PhraseP ![PatternAtom]
             deriving (Show)

data Binding = SigB !Ident !Type
             | ValB !Ident !Expr
             | SampleB !Ident !Expr
             | TabB ![(Ident, Maybe Type)] [TabulatedFun]
             deriving (Show)

data TabulatedFun = TabulatedFun !Ident !TabSample
                  deriving (Show)

data TabSample = TabSample ![TabSelector] !Expr
               deriving (Show)

data TabSelector = TabIndex !Ident
                 deriving (Show)
