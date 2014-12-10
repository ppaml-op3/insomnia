module Insomnia.SurfaceSyntax.Syntax where

import Data.Monoid ((<>))

import Insomnia.Common.Literal
import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.SurfaceSyntax.FixityParser (Fixity)

type Ident = String

type Nat = Integer

data QualifiedIdent = QId ![Ident] !Ident
                    deriving (Show)

newtype Con = Con { unCon :: QualifiedIdent }
            deriving (Show, Eq, Ord)

newtype TyVar = TyVar { unTyVar :: Ident }
              deriving (Show)

newtype Var = Var { unVar :: Ident }
            deriving (Show)

newtype QVar  = QVar { unQVar :: QualifiedIdent }
             deriving (Show)

instance Ord QualifiedIdent where
  (QId p1 f1) `compare` (QId p2 f2) = compare p1 p2 <> compare f1 f2

instance Eq QualifiedIdent where
  q1 == q2 = compare q1 q2 == EQ

data Toplevel = Toplevel ![ToplevelItem]
              deriving (Show)

data ToplevelItem =
  ToplevelModel !Ident !(Maybe ModuleType) !ModelExpr
  | ToplevelModuleType !Ident !ModuleType
    deriving (Show)

data ModelExpr =
  ModelStruct !Model
  | ModelSeal !ModelExpr !ModuleType
  | ModelAssume !ModuleType
  | ModelId !QualifiedIdent
    deriving (Show)
             
data ModuleType =
  SigMT !Signature !ModuleKind
  | IdentMT !Ident
    deriving (Show)



data Signature = Sig ![SigDecl]
               deriving (Show)

data SigDecl = ValueSig !Stochasticity !Ident !Type
             | FixitySig !Ident !Fixity
             | TypeSig !Ident !TypeSigDecl
             | SubmoduleSig !Ident !ModuleType
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

type KindedTVar = (TyVar,Kind)

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
  | ParameterDecl !Expr
  | ValDecl !Expr
  | SampleDecl !Expr
  | SigDecl !Stochasticity !Type
  deriving (Show)

data Kind = KType | KArr !Kind !Kind
          deriving (Show)

data TypeAtom = TC !Con
              | TV !TyVar
              | TEnclosed !Type !(Maybe Kind)  -- '(' Type ')' or '(' Type ':' Kind ')'
              | TRecord !Row
              deriving (Show)

newtype Label = Label { labelName :: String }
              deriving (Show)

data Row = Row ![(Label, Type)]
         deriving (Show)

data Type = TPhrase ![TypeAtom]
          | TForall !TyVar !Kind !Type
          deriving (Show)

data Notation a = PrefixN !a
                | InfixN !a
                deriving (Show)
                         
data Identifier = V !Var
              | Q !QVar
              | C !Con
              deriving (Show)

data ExprAtom = I !(Notation Identifier)
              | L !Literal
              | Record ![(Label, Expr)]
              | Enclosed !Expr !(Maybe Type) -- '(' Expr ')' or '(' Expr ':' Type ')'
              | Return !ExprAtom
              deriving (Show)

data Expr = Phrase ![ExprAtom]
          | Lam !Ident !(Maybe Type) !Expr
          | Case !Expr ![Clause]
          | Let ![Binding] !Expr
          deriving (Show)

data Clause = Clause !Pattern !Expr
            deriving (Show)

data PatternAtom = WildcardP
                 | VarP !Var
                 | ConP !(Notation Con)
                 | RecordP ![(Label, Pattern)]
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
