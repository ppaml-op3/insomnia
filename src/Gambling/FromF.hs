{-# LANGUAGE TypeFamilies, FlexibleInstances #-}
module Gambling.FromF where

import Control.Applicative
import Control.Monad.Reader hiding (forM)
import Data.Function (on)
import Data.List (sortBy)
import Data.Traversable


import Unbound.Generics.LocallyNameless

import Insomnia.Common.Literal
import Insomnia.Common.SampleParameters

import qualified Gambling.Racket as R
import FOmega.Syntax

fomegaToGamble :: String -> Command -> R.Module
fomegaToGamble modName c =
  runLFreshM $ runReaderT comp ()
  where
    comp = do
      mdefns <- gamble (Outer c)
      let reqs =
            [
              R.RequireMB $ R.RequiresAll (embed "boot.rkt")
            ]
          defns = reqs ++ mdefns
      return $ R.Module (s2n modName) "gamble" $ R.ModuleDefnCtx $ bind (rec defns) R.ProvidesAll

-- newtype wrapper to distinguish Commands at the toplevel vs nest in the LHS of a bind.
newtype Outer a = Outer {getOutter :: a}


type M = ReaderT Context LFreshM

type Context = ()

class Gamble i where
  type Gambled i :: *
  gamble :: i -> M (Gambled i)

-- dangerous!
unsafeCoerceName :: Name a -> Name b
unsafeCoerceName nm = makeName (name2String nm) (name2Integer nm)

lookupVar :: Var -> M R.Var
lookupVar = return . unsafeCoerceName

associate :: Var -> M R.Var
associate = return . unsafeCoerceName

simpleBody :: R.Expr -> R.Body
simpleBody = R.Body . bind (rec []) 

instance Gamble Literal where
  type Gambled Literal = Literal
  gamble = return

instance Gamble Term where
  type Gambled Term = R.Expr
  gamble (V x) = R.Var <$> lookupVar x
  gamble (L lit) = R.Literal <$> gamble lit
  gamble (Lam bnd) = lunbind bnd $ \((x, _ty), body) -> do
    x' <- associate x
    R.Lam . bind [x'] . simpleBody <$> gamble body
  gamble (PLam bnd) = lunbind bnd $ \((_tv, _k), body) -> do
    R.Lam . bind [] . simpleBody <$> gamble body
  gamble (PApp m _ty) = papp <$> gamble m
    where papp e = R.App [e]
  gamble (App m1 m2) = app <$> gamble m1 <*> gamble m2
    where app e1 e2 = R.App [e1, e2]
  gamble (Let bnd) = lunbind bnd $ \((x, m1), body) -> do
    m1' <- gamble (unembed m1)
    x' <- associate x
    R.Let . bind [R.Binding x' $ embed m1'] . simpleBody <$> gamble body
  gamble (Pack _hidTy m _asTy) = gamble m
  gamble (Unpack bnd) = lunbind bnd $ \((_tv, x, m1), body) -> do
    m1' <- gamble (unembed m1)
    x' <- associate x
    R.Let . bind [R.Binding x' $ embed m1'] . simpleBody <$> gamble body
  gamble (Return m) = do
    gambleReturn <$> gamble m
  gamble (LetSample bnd) = lunbind bnd $ \((x, m1), m2) ->
    gambleBind <$> associate x
    <*> gamble (unembed m1)
    <*> gamble m2
  gamble (LetRec bnd) = lunbind bnd $ \(recBnds, body) -> do
    recBnds' <- forM (unrec recBnds) $ \(x, _tp, m) -> do
      x' <- associate x
      e <- gamble (unembed m)
      return $ R.Binding x' (embed e)
    body' <- gamble body
    return $ R.LetRec $ bind (rec recBnds') $ simpleBody body'
  gamble (Record fs) =
    case sniffFields fs of
     Tuplish vs -> gambleImmutableVector <$> traverse gamble vs
     Recordish sfs -> fmap gambleImmutableHash $ forM sfs $ \(s, m) -> do
       e <- gamble m
       return (R.StringLit s, e)
     Boring -> return $ gambleNull
     Valueish m -> gamble m
     DataInOutish mIn mOut -> gambleInOutPair <$> gamble mIn <*> gamble mOut
     Consish cs -> fmap gambleImmutableHash $ forM cs $ \(c, m) -> do
       e <- gamble m
       return (R.QuoteSymbol c, e)
  gamble (Proj m f) =
    case f of
     FUser s -> gambleHashRef (R.StringLit s) <$> gamble m
     FVal -> gamble m
     FCon c -> gambleHashRef (R.QuoteSymbol c) <$> gamble m
     FDataIn -> gambleProjectDataIn <$> gamble m
     FDataOut -> gambleProjectDataOut <$> gamble m
  gamble (Unroll _muTy m _ctxTy) = gamble m
  gamble (Roll _muty m _ctxTy) = gamble m
  gamble (Inj c m _sumTy) = do
    e <- gamble m
    s <- case c of
     FCon c -> return $ R.QuoteSymbol c
    return $ gambleCons s e
  gamble (Case subj clauses defaultClause) = do
    subj' <- gamble subj
    clauses' <- traverse gamble clauses
    defaultClause' <- gamble (DefaultClause defaultClause)
    return $ R.Match subj' (clauses' ++ defaultClause')
  gamble m = error $ "Gamble.gamble " ++ show m ++ " unimplemented"

newtype DefaultClause a = DefaultClause a

instance Gamble (DefaultClause (Maybe Term)) where
  type Gambled (DefaultClause (Maybe Term)) = [R.Clause]
  gamble (DefaultClause Nothing) = return []
  gamble (DefaultClause (Just m)) = do
    e <- gamble m
    return [R.Clause $ bind R.WildP $ simpleBody e]

instance Gamble Clause where
  type Gambled Clause = R.Clause
  gamble (Clause fld bnd) = lunbind bnd $ \(x, m) -> do
    f' <- case fld of
           FCon f -> return f
    x' <- associate x
    e <- gamble m
    return $ R.Clause $ bind (R.ConsP (R.QuoteSymbolP $ embed f') (R.VarP x')) $ simpleBody e

-- implement "return m" as "(lambda () e)"
gambleReturn :: R.Expr -> R.Expr
gambleReturn = R.Lam . bind [] . simpleBody

-- implement "let x ~ m1 in m2" as "(lambda () (let ([x' (e1)]) (e2)))"
gambleBind :: R.Var -> R.Expr -> R.Expr -> R.Expr
gambleBind x e1 e2 = R.Lam . bind [] . simpleBody
                     $ R.Let $ bind
                     [R.Binding x (embed $ R.App [e1])]
                     (simpleBody $ R.App [e2])

-- force a distribution monad thunk "m" as "(e)"
gambleForce :: R.Expr -> R.Expr
gambleForce e = R.App [e]

gambleNull :: R.Expr
gambleNull = R.Var (s2n "null")

-- compile constructor C applied to value m as "(cons 'C m)"
gambleCons :: R.Expr -> R.Expr -> R.Expr
gambleCons c s = R.App [R.Var (s2n "cons")
                       , c
                       , s
                       ]

-- gamble's sampler
--  (mh-sample e)
gambleSampler :: SampleParameters -> R.Expr -> R.Expr
gambleSampler _params e = R.App [R.Var (s2n "mh-sampler"), e]

-- | implement tuples as immutable vectors
gambleImmutableVector :: [R.Expr] -> R.Expr
gambleImmutableVector es = R.App (R.Var (s2n "vector-immutable") : es)

gambleImmutableHash :: [(R.Expr, R.Expr)] -> R.Expr
gambleImmutableHash ses = R.App (R.Var (s2n "hash") : concat (map kv ses))
  where
    kv (k, v) = [k, v]

gambleHashRef :: R.Expr -> R.Expr -> R.Expr
gambleHashRef k e = R.App [R.Var (s2n "hash-ref")
                          , e
                          , k]

gambleInOutPair :: R.Expr -> R.Expr -> R.Expr
gambleInOutPair eIn eOut = R.App [R.Var (s2n "vector-immutable")
                                 , eIn
                                 , eOut
                                 ]

gambleProjectDataIn :: R.Expr -> R.Expr
gambleProjectDataIn e = R.App [R.Var (s2n "vector-ref")
                              , e
                              , R.Literal (IntL 0)
                              ]

gambleProjectDataOut :: R.Expr -> R.Expr
gambleProjectDataOut e = R.App [R.Var (s2n "vector-ref")
                               , e
                               , R.Literal (IntL 1)
                               ]



singleton :: a -> [a]
singleton x = [x]

instance Gamble (Outer Command) where
  type Gambled (Outer Command) = [R.ModuleBinding]
  gamble (Outer (EffectC _pc m)) =
    singleton . R.ExprMB . embed <$> gamble m  -- TODO XXX use the command
  gamble (Outer (ReturnC _m)) = return [] -- ignore the return at the end of the whole program
  gamble (Outer (LetC bnd)) =
    lunbind bnd $ \((x, m), c) -> do
      x' <- associate x
      e <- gamble (unembed m)
      let mb = R.DefnMB $ R.Define $ rebind x' (embed e)
      mbs <- gamble (Outer c)
      return (mb:mbs)
  gamble (Outer (BindC bnd)) =
    lunbind bnd $ \((x, c1), c2) -> do
      x' <- associate x
      e <- gamble (unembed c1)
      let mb = R.DefnMB $ R.Define $ rebind x' (embed e)
      mbs <- gamble (Outer c2)
      return (mb:mbs)
  gamble (Outer (UnpackC bnd)) =
    lunbind bnd $ \((_tv, x, m), c) -> do
      x' <- associate x
      e <- gamble (unembed m)
      let mb = R.DefnMB $ R.Define $ rebind x' (embed e)
      mbs <- gamble (Outer c)
      return (mb:mbs)

instance Gamble Command where
  type Gambled Command = R.Expr
  gamble (EffectC (SamplePC params) m) = do
    e <- gambleForce <$> gamble m
    return (gambleSampler params e)
  gamble (EffectC PrintPC m) = gambleForce <$> gamble m
  gamble (ReturnC m) = gamble m
  gamble (LetC bnd) = lunbind bnd $ \((x, m), c) -> do
    x' <- associate x
    e1 <- gamble (unembed m)
    R.Let . bind [R.Binding x' $ embed e1] . simpleBody <$> gamble c
  gamble (BindC bnd) = lunbind bnd $ \((x, c1), c2) -> do
    x' <- associate x
    e1 <- gamble (unembed c1)
    R.Let . bind [R.Binding x' $ embed e1] . simpleBody <$> gamble c2
    
  
sniffFields :: [(Field, Term)] -> Recordsy Term
sniffFields [] = Boring
sniffFields ((FUser u, m):rest) = Recordish $ (u,m):expectRecordish rest
sniffFields ((FTuple i, m):rest) = Tuplish  . map snd . sortBy (compare `on` fst)
                                   $ (i,m):expectTuplish rest
sniffFields ((FCon c, m):rest) = Consish $ (c,m):expectConsish rest
sniffFields [(FDataIn, mIn), (FDataOut, mOut)] = DataInOutish mIn mOut
sniffFields [(FDataOut, mOut), (FDataIn, mIn)] = DataInOutish mIn mOut
sniffFields [(FType, _)] = Boring
sniffFields [(FSig, _)] = Boring
sniffFields [(FVal, m)] = Valueish m

-- take apart a record where we expect to see only user-supplied fields
expectRecordish :: [(Field, Term)] -> [(String, Term)]
expectRecordish [] = []
expectRecordish ((FUser u, m):rest) = (u,m):expectRecordish rest

expectTuplish :: [(Field, Term)] -> [(Int, Term)]
expectTuplish [] = []
expectTuplish ((FTuple i, m):rest) = (i,m):expectTuplish rest

expectConsish :: [(Field, Term)] -> [(String, Term)]
expectConsish [] = []
expectConsish ((FCon c, m):rest) = (c,m):expectConsish rest

-- ugh
data Recordsy a =
  Tuplish [a]
  | Recordish [(String, a)]
  | Boring
  | DataInOutish a a -- in, out
  | Consish [(String, a)]
  | Valueish a
