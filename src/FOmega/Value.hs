{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module FOmega.Value where

import Control.Lens
import Data.Monoid (Monoid(..), (<>), Endo(..))

import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal
import Insomnia.Pretty

import FOmega.Syntax
import FOmega.Pretty

data Value =
  RecordV ![(Field, Value)]
  | InjV !Field !Value
  | PClosureV !Env !PolyClosure
  | ClosureV !LambdaClosure
  | DistV !DistClosure
  | LitV !Literal
  | PackV !Type !Value
  | RollV !Value

data Closure =
  PlainLambdaClz !(Bind Var Term)
  | PrimitiveClz !PrimitiveClosure
--  | MemoizedFnRef !(IORef Value)

data PolyClosure =
  PlainPolyClz !(Bind TyVar Term)
  | PrimitivePolyClz !PolyPrimitiveClosure

type PrimitiveClosureHead = String

data LambdaClosure =
  LambdaClosure
  { _lambdaClosureEnv :: !Env
  , _lambdaClosureClz :: !Closure
  }

-- the number is a count of type arguments.  Note that we assume a type erasure impl,
-- so the types simply get thrown away.
data PolyPrimitiveClosure =
  PolyPrimitiveClosure
  { _polyPrimClz :: !PrimitiveClosure
  , _polyPrimSatArity :: !Int
  }
  
-- (possibly partially applied) primitives
data PrimitiveClosure =
  PrimitiveClosure {
    _primClzHead :: PrimitiveClosureHead
    , _primClzSatArity :: Int -- number of arguments needed before saturation, always >= 1
    , _primClzSpine :: PrimitiveClosureSpine
    }

data PrimitiveClosureSpine =
  NilPCS
  | AppPCS !PrimitiveClosureSpine !Value

infixl 5 `AppPCS`

data DistClosure =
  DistClosure {
    _distClosureEnv :: !Env
    , _distClosureThunk :: !DistThunk
    }

data DistThunk =
  ReturnTh !Term
  | LetSampleTh !(Bind (Var, Embed Term) Term)
  | MemoTh !Term
  | PrimitiveTh !PrimitiveDistribution

data PrimitiveDistribution =
  ChoosePD !Double !DistClosure !DistClosure
  | UniformPD !Double !Double -- lo, hi
  | NormalPD !Double !Double -- mu, sigma^2
  | PosteriorPD !LambdaClosure !Value !DistClosure

newtype Env = Env { envLookup :: Var -> Value }

$(makeLenses ''LambdaClosure)
$(makeLenses ''PrimitiveClosure)
$(makeLenses ''PolyPrimitiveClosure)
$(makeLenses ''DistClosure)

tupleV :: [Value] -> Value
tupleV vs = RecordV $ zipWith (\v n -> (FTuple n, v)) vs [0..]

emptyEnv :: Env
emptyEnv = Env (const (error "unbound variable in FOmega.Eval baseEnv"))

instance Show Value where
  showsPrec d v_ =
    case v_ of
     RecordV fvs -> showParen (d > 10) (showString "RecordV " . showsPrec 11 fvs)
     InjV f v -> showParen (d > 10) 
                (showString "InjV " . showsPrec 11 f
                 .showString " "
                 . showsPrec 11 v)
     PClosureV {} -> showString "≪Λ…≫"
     ClosureV clz -> showsPrec d clz
     DistV {} -> showString "≪D…≫"
     LitV l -> showParen (d > 10) (showString "LitV " . showsPrec 11 l)
     PackV t m -> showParen (d > 10) (showString "PackV " . showsPrec 11 t
                                      . showString " "
                                      . showsPrec 11 m)
     RollV m -> showParen (d > 10) (showString "RollV " . showsPrec 11 m)

instance Show LambdaClosure where
  showsPrec d v =
    showsPrec d (v^.lambdaClosureClz)

instance Show Closure where
  showsPrec d v_ =
    case v_ of
     PlainLambdaClz {} -> showString "≪λ…≫"
     PrimitiveClz p -> showsPrec d p

instance Show PrimitiveClosure where
  showsPrec _ (PrimitiveClosure h n sp) =
    showString "≪"
    . showString h
    . showString " "
    . showsPrec 10 sp
    . showString " "
    . showsPrec 10 n
    . showString "≫"

instance Show PrimitiveClosureSpine where
  showsPrec d sp_ =
    case sp_ of
     NilPCS -> id
     AppPCS sp v -> showsPrec 10 sp . showParen (d > 10) (showsPrec 11 v)

instance Pretty Value where
  pp (RecordV fvs) =
    let
      ppF (f, v) = fsep [ppField f, indent "=" (pp v)]
    in
     braces $ fsep $ punctuate "," $ map ppF fvs
  pp (InjV f v) = precParens 2 $ fsep ["inj", ppField f, pp v]
  pp (PClosureV {}) = "≪Λ…≫"
  pp (ClosureV clz) = pp clz
  pp (DistV {}) = "≪D…≫"
  pp (LitV l) = pp l
  pp (PackV t v) = precParens 2 $ fsep ["pack", withPrec 2 AssocLeft (Right $ ppType t)
                                       , indent "," (pp v)]
  pp (RollV v) = precParens 2 $ fsep ["pack", pp v]

instance Pretty LambdaClosure where
  pp v = pp (v^.lambdaClosureClz)

instance Pretty Closure where
  pp (PlainLambdaClz {}) = "≪λ…≫"
  pp (PrimitiveClz p) = pp p

instance Pretty PrimitiveClosure where
  pp (PrimitiveClosure h n sp_) =
    doubleAngles $ fsep $ [pp h] ++ appEndo (ppSpine sp_) (replicate n "_")
    where
      doubleAngles p = "≪" <> p <> "≫"
      ppCons p = Endo ((:) p)
    
      ppSpine NilPCS = mempty
      ppSpine (AppPCS sp v) = ppSpine sp
                              <> ppCons (pp v)
