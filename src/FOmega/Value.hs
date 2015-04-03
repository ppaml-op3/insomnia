{-# LANGUAGE OverloadedStrings #-}
module FOmega.Value where

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal
import Insomnia.Pretty

import FOmega.Syntax
import FOmega.Pretty

data Value =
  RecordV ![(Field, Value)]
  | InjV !Field !Value
  | PClosureV !Env !(Bind TyVar Term)
  | ClosureV !Env !Closure
  | DistV !Env !DistThunk
  | LitV !Literal
  | PackV !Type !Value
  | RollV !Value

data Closure =
  PlainLambdaClz !(Bind Var Term)
  | PrimitiveClz !String
--  | MemoizedFnRef !(IORef Value)

data DistThunk =
  ReturnTh !Term
  | LetSampleTh !(Bind (Var, Embed Term) Term)
  | MemoTh !Term
  | PrimitiveTh !String

newtype Env = Env { envLookup :: Var -> Value }

tupleV :: [Value] -> Value
tupleV vs = RecordV $ zipWith (\v n -> (FTuple n, v)) vs [0..]

instance Show Value where
  showsPrec d v_ =
    case v_ of
     RecordV fvs -> showParen (d > 10) (showString "RecordV " . showsPrec 10 fvs)
     InjV f v -> showParen (d > 10) 
                (showString "InjV " . showsPrec 10 f
                 . showsPrec 10 v)
     PClosureV {} -> showString "≪Λ…≫"
     ClosureV {} -> showString "≪λ…≫"
     DistV {} -> showString "≪D…≫"
     LitV l -> showParen (d > 10) (showString "LitV " . showsPrec 10 l)
     PackV t m -> showParen (d > 10) (showString "PackV " . showsPrec 10 t . showsPrec 10 m)
     RollV m -> showParen (d > 10) (showString "RollV " . showsPrec 10 m)

instance Pretty Value where
  pp (RecordV fvs) =
    let
      ppF (f, v) = fsep [ppField f, indent "=" (pp v)]
    in
     braces $ fsep $ punctuate "," $ map ppF fvs
  pp (InjV f v) = precParens 2 $ fsep ["inj", ppField f, pp v]
  pp (PClosureV {}) = "≪Λ…≫"
  pp (ClosureV {}) = "≪λ…≫"
  pp (DistV {}) = "≪D…≫"
  pp (LitV l) = pp l
  pp (PackV t v) = precParens 2 $ fsep ["pack", withPrec 2 AssocLeft (Right $ ppType t)
                                       , indent "," (pp v)]
  pp (RollV v) = precParens 2 $ fsep ["pack", pp v]
