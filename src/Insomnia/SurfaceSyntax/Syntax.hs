module Insomnia.SurfaceSyntax.Syntax where

import Data.Monoid ((<>))

import Insomnia.Common.Literal
import Insomnia.Common.Stochasticity
import Insomnia.Common.ModuleKind
import Insomnia.Common.SampleParameters
import Insomnia.SurfaceSyntax.FixityParser (Fixity)
import Insomnia.SurfaceSyntax.SourcePos

type Ident = String

type Nat = Integer

data QualifiedIdent = QId ![Ident] !Ident
                    deriving (Show)

newtype Con = Con { unCon :: QualifiedIdent }
            deriving (Show, Eq, Ord)

newtype TyVar = TyVar { unTyVar :: Ident }
              deriving (Show)

newtype Var = Var { unVar :: QualifiedIdent }
            deriving (Show, Eq, Ord)

instance Ord QualifiedIdent where
  (QId p1 f1) `compare` (QId p2 f2) = compare p1 p2 <> compare f1 f2

instance Eq QualifiedIdent where
  q1 == q2 = compare q1 q2 == EQ

data Toplevel = Toplevel ![ToplevelItem]
              deriving (Show)

data ToplevelItem_ =
  ToplevelBigExpr !Ident !BigExpr
  | ToplevelImport !ImportFileSpec ![ImportSpecItem]
  | ToplevelQuery !QueryExpr
    deriving (Show)

type ToplevelItem = Positioned ToplevelItem_

-- | "big" expressions - module or module type expression syntax
data BigExpr =
  LiteralBE !ModuleKind !Module -- module/model { defns }
  | ClassifierBE !ModuleKind !Signature -- module/model type { decls }
  | VarBE !QualifiedIdent -- M.M' or S
  | AppBE !QualifiedIdent ![QualifiedIdent] -- F (X, Y, Z)
  | AbsBE ![(Ident, BigExpr)] !BigExpr -- (X : S, Y : S') -> M or S
  | LocalBE !Module !BigExpr !BigExpr -- "local decls in M : S"
  | SealBE !BigExpr !BigExpr -- M : S
  | WhereTypeBE !BigExpr !WhereClause -- S where type t = P.t'
  | AssumeBE !BigExpr -- assume S
    deriving (Show)


newtype ImportFileSpec = ImportFileSpec { importFileSpecPath :: FilePath }
                       deriving (Show)

data ImportSpecItem =
  ImportModuleSpecItem !Ident !Ident
  | ImportModuleTypeSpecItem !Ident 
  deriving (Show)

data QueryExpr =
  GenSamplesQE !QualifiedIdent !SampleParameters
  deriving (Show)

data WhereClause =
  WhereTypeCls !Con !Type
    deriving (Show)

data Signature = Sig ![SigDecl]
               deriving (Show)

data SigDecl = ValueSig !(Maybe Stochasticity) !Ident !Type
             | FixitySig !Ident !Fixity
             | TypeSig !Ident !TypeSigDecl
             | SubmoduleSig !Ident !BigExpr
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

data Module = Module ![Decl]
           deriving (Show)

data Decl = ValueDecl !Ident !ValueDecl
          | ImportDecl !QualifiedIdent
          | TypeDefn !Ident !TypeDefn
          | TypeAliasDefn !Ident !TypeAlias
          | BigSubmoduleDefn !Ident !BigExpr
          | BigSampleDefn !Ident !BigExpr
          | FixityDecl !Ident !Fixity
          | TabulatedSampleDecl !TabulatedDecl
          deriving (Show)

data ValueDecl =
  FunDecl !Expr
  -- parameters, random variables, or "figure it out from context"
  | ValDecl !(Maybe Stochasticity) !Expr
  | SampleDecl !Expr
  | SigDecl !(Maybe Stochasticity) !Type
  deriving (Show)

data Kind = KType | KArr !Kind !Kind
          deriving (Show)

data TypeAtom = TC !(Notation Con)
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
                         
data ExprAtom = V !(Notation Var)
              | C !(Notation Con)
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
                 | VarP !Ident
                 | ConP !(Notation Con)
                 | RecordP ![(Label, Pattern)]
                 | EnclosedP !Pattern
                  deriving (Show)

data Pattern = PhraseP ![PatternAtom]
             deriving (Show)

data Binding = SigB !Ident !Type
             | ValB !Ident !Expr
             | SampleB !Ident !Expr
             | TabB !TabulatedDecl
             deriving (Show)

-- "forall ids . tabfuns"
data TabulatedDecl = TabulatedDecl ![(Ident, Maybe Type)] ![TabulatedFun]
                   deriving (Show)

data TabulatedFun = TabulatedFun !Ident !TabSample
                  deriving (Show)

data TabSample = TabSample ![TabSelector] !Expr
               deriving (Show)

data TabSelector = TabIndex !Ident
                 deriving (Show)
