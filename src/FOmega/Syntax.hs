{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
      MultiParamTypeClasses, FlexibleInstances
  #-}
module FOmega.Syntax where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Insomnia.Common.Literal
import Insomnia.Common.SampleParameters

import Unbound.Generics.LocallyNameless
import {-# SOURCE #-} FOmega.Pretty (ppType, ppTerm, ppKind, ppCommand)
import Insomnia.Pretty (Pretty(..))

-- | There will be some stylized records that have predefined field
-- names distinct from what a user may write.
data Field =
  FVal
  | FType
  | FSig
  -- data type definition fields
  | FDataOut
  | FDataIn
  -- data type constructor field
  | FCon !String
  -- integer indexed field
  | FTuple !Int
  -- user defined record fields
  | FUser !String
    deriving (Show, Eq, Ord, Typeable, Generic)

data Kind =
  KType
  | KArr !Kind !Kind
    deriving (Show, Eq, Typeable, Generic)

type TyVar = Name Type

-- TODO: Maybe use a (βη)-normalized representation?
data Type =
  TV !TyVar
  | TLam !(Bind (TyVar, Embed Kind) Type)
  | TApp !Type !Type
  | TForall !(Bind (TyVar, Embed Kind) Type)
  | TFix !(Bind (TyVar, Embed Kind) Type)
  | TExist !ExistPack
  | TRecord ![(Field, Type)] -- TRecord [] is the unit type
  | TSum ![(Field, Type)] -- TSum [] is the void type
  | TArr !Type !Type
  | TDist !Type -- probability distribution monad
                        
  deriving (Show, Typeable, Generic)

type ExistPack = Bind (TyVar, Embed Kind) Type

type Var = Name Term

data Term =
  V !Var
  | L !Literal
  | Lam !(Bind (Var, Embed Type) Term)
  | App !Term !Term
  | Let !(Bind (Var, Embed Term) Term)
  | PLam !(Bind (TyVar, Embed Kind) Term)
  | PApp !Term !Type
  | Record ![(Field, Term)] -- Record [] is the unit value
  | Proj !Term !Field
  | Pack !Type !Term !ExistPack
  | Unpack !(Bind (TyVar, Var, Embed Term) Term)
  | Return !Term
  | LetSample !(Bind (Var, Embed Term) Term)
  | LetRec !(Bind RecBindings Term)
  | Memo !Term
  | Assume !Type
  | Inj !Field !Term !Type
  | Case !Term ![Clause] !(Maybe Term)
  | Roll !Type !Term !(Bind TyVar Type) -- roll μ..., m as δ.T
  | Unroll !Type !Term !(Bind TyVar Type) -- unroll μ..., m as δ.T
  | Abort !Type
  deriving (Show, Typeable, Generic)

data Command =
  LetC !(Bind (Var, Embed Term) Command)
  | UnpackC !(Bind (TyVar, Var, Embed Term) Command)
  | BindC !(Bind (Var, Embed Command) Command)
  | ReturnC !Term
  | EffectC !PrimitiveCommand !Term
  deriving (Show, Typeable, Generic)

data PrimitiveCommand =
  SamplePC SampleParameters
  | PrintPC 
  deriving (Show, Typeable, Generic)

infixl 6 `Proj` 

data Clause = Clause !Field !(Bind Var Term)
            deriving (Show, Typeable, Generic)

-- terms should be values
type RecBindings = Rec [(Var, Embed Type, Embed Term)]


-- * Alpha equivalence and Substitution

instance Alpha Field
instance Alpha Kind
instance Alpha Type
instance Alpha Term
instance Alpha Clause
instance Alpha Command
instance Alpha PrimitiveCommand

instance Subst Type Type where
  isvar (TV a) = Just (SubstName a)
  isvar _ = Nothing

-- no types inside kinds
instance Subst Type Kind where
  subst _ _ = id
  substs _ = id
instance Subst Type Field where
  subst _ _ = id
  substs _ = id

instance Subst Type Literal where
  subst _ _ = id
  substs _ = id

instance Subst Type Clause

instance Subst Type Term

instance Subst Type Command


instance Subst Term Term where
  isvar (V a) = Just (SubstName a)
  isvar _ = Nothing

instance Subst Term Clause

instance Subst Term Type where
  subst _ _ = id
  substs _ = id

instance Subst Term Field where
  subst _ _ = id
  substs _ = id

instance Subst Term Kind where
  subst _ _ = id
  substs _ = id

instance Subst Term Literal where
  subst _ _ = id
  substs _ = id

instance Subst Term Command

instance Subst b PrimitiveCommand where
  subst _ _ = id
  substs _ = id

-- * Pretty printing

instance Pretty Kind where pp = ppKind
instance Pretty Type where pp = ppType
instance Pretty Term where pp = ppTerm
instance Pretty Command where pp = ppCommand

-- * Utilities

kArrs :: [Kind] -> Kind -> Kind
kArrs [] = id
kArrs (k:ks) = KArr k . kArrs ks

intT :: Type
intT = TV (s2n "Int")

realT :: Type
realT = TV (s2n "Real")

tLams :: [(TyVar, Kind)] -> Type -> Type
tLams [] = id
tLams ((tv,k):tvks) =
  TLam . bind (tv, embed k) . tLams tvks

tLams' :: [(TyVar, Embed Kind)] -> Type -> Type
tLams' [] = id
tLams' (tvk:tvks) =
  TLam . bind tvk . tLams' tvks

tForalls :: [(TyVar, Kind)] -> Type -> Type
tForalls [] = id
tForalls ((tv,k):tvks) =
  TForall . bind (tv, embed k) . tForalls tvks

tExists :: [(TyVar, Kind)] -> Type -> Type
tExists [] = id
tExists ((tv,k):tvks) =
  TExist . bind (tv, embed k) . tExists tvks

tExists' :: [(TyVar, Embed Kind)] -> Type -> Type
tExists' [] = id
tExists' (tvk:tvks) =
  TExist . bind tvk . tExists' tvks

tApps :: Type -> [Type] -> Type
tApps = flip tApps'
  where
    tApps' [] = id
    tApps' (t:ts) = tApps' ts . (`TApp` t)

tArrs :: [Type] -> Type -> Type
tArrs [] = id
tArrs (t:ts) = (t `TArr`) . tArrs ts

tupleT :: [Type] -> Type
tupleT ts =
  let fts = zipWith (\t i -> (FTuple i, t)) ts [0..]
  in TRecord fts

lams :: [(Var, Type)] -> Term -> Term
lams [] = id
lams ((v,t):vts) =
  Lam . bind (v, embed t) . lams vts

lams' :: [(Var, Embed Type)] -> Term -> Term
lams' [] = id
lams' (vt:vts) =
  Lam . bind vt . lams' vts

pLams :: [(TyVar, Kind)] -> Term -> Term
pLams [] = id
pLams ((tv,k):tvks) =
  PLam . bind (tv, embed k) . pLams tvks

pLams' :: [(TyVar, Embed Kind)] -> Term -> Term
pLams' [] = id
pLams' (tvk:tvks) =
  PLam . bind tvk . pLams' tvks


pApps :: Term -> [Type] -> Term
pApps = flip pApps'
  where
    pApps' [] = id
    pApps' (t:ts) = pApps' ts . (`PApp` t)

apps :: Term -> [Term] -> Term
apps = flip apps'
  where
    apps' [] = id
    apps' (m:ms) = apps' ms . (`App` m)

-- | packs τs, e as αs.τ' defined as
-- packs ε, e as ·.τ ≙ e
-- packs τ:τs, e as α,αs.τ' ≙ pack τ, (packs τs, e as αs.τ'[τ/α]) as α.∃αs.τ'
packs :: [Type] -> Term -> ([(TyVar, Embed Kind)], Type) -> Term
packs taus_ m_ (tvks_, tbody_) =
  go taus_ tvks_ tbody_ m_
  where
    go [] [] _t m = m
    go (tau:taus) (tvk@(tv,_k):tvks') tbody m =
      let m' = go taus tvks' (subst tv tau tbody) m
          t' = tExists' tvks' tbody
      in Pack tau m' (bind tvk t')
    go _ _ _ _ = error "expected lists of equal length"

unpacksM :: LFresh m => [TyVar] -> Var -> m ((Term -> Term -> Term), [AnyName])
unpacksM [] x = return ((\e1 ebody -> Let $ bind (x, embed e1) ebody),
                        [])
unpacksM (tv:tvs) x = do
  x1 <- lfresh x
  let avd = [AnyName x1]
  (rest, avd') <- avoid avd (unpacksM tvs x)
  return ((\e1 -> Unpack . bind (tv, x1, embed e1) . rest (V x1)),
          avd ++ avd')

unpacksCM :: LFresh m => [TyVar] -> Var -> m ((Term -> Command -> Command), [AnyName])
unpacksCM [] x = return ((\e1 cbody -> LetC $ bind (x, embed e1) cbody),
                         [])
unpacksCM (tv:tvs) x = do
  x1 <- lfresh x
  let avd = [AnyName x1]
  (rest, avd') <- avoid avd (unpacksCM tvs x)
  return ((\e1 -> UnpackC . bind (tv, x1, embed e1) . rest (V x1)),
          avd ++ avd')


unpacks :: LFresh m => [TyVar] -> Var -> Term -> Term -> m Term
unpacks tvs x e1 ebody = do
  (rest, _) <- unpacksM tvs x
  return $ rest e1 ebody

lets :: [(Var, Term)] -> Term -> Term
lets [] = id
lets ((v,m):vs) = Let . bind (v, embed m) . lets vs


tuple :: [Term] -> Term
tuple ms = 
  let ims = zipWith (\m i -> (FTuple i, m)) ms [0..]
  in Record ims

unitT :: Type
unitT = TRecord []

unitVal :: Term
unitVal = Record []


voidT :: Type
voidT = TSum []

-- | λε:⋆. { Nil : {} | Cons : { #0 : τ; #1 : (listT τ) } }
listSumT :: Type
listSumT  =
  let
    ve = s2n "ε"
    e = TV ve
  in
   TLam $ bind (ve, embed KType)
   $ TSum [(FUser "Nil", unitT)
          , (FUser "Cons", tupleT [e, listT `TApp` e])]

-- μ (δ : ⋆→⋆) . λ (α : ⋆) . { Nil : {} | Cons : { #0 : α; #1 : δ α } }
listT :: Type
listT =
  let
    vd = s2n "δ"
    va = s2n "α"
    d = TV vd
    a = TV va

    body = TSum [(FUser "Nil", unitT)
                , (FUser "Cons", tupleT [a, d `TApp` a])]

    l = TLam $ bind (va, embed KType) body
  in
   TFix $ bind (vd, embed (KType `KArr` KType)) l


-- | λ _ : ()  . abort T
abortThunk :: Type -> Term
abortThunk = Lam . bind (s2n "_abort", embed unitT) . Abort

-- | construct: Λε:⋆ . roll (listT ε) (Inj Nil [] (listSumT ε)) as α.(α ε)
nilListVal :: Term
nilListVal =
  let
    ve = s2n "ε"
    va = s2n "α"
    e = TV ve
    a = TV va
    inj = Inj (FUser "Nil") unitVal (listSumT `TApp` e)
    ctx = bind va (a `TApp` e)
  in PLam $ bind (ve, embed KType)
     $ Roll (listT `TApp` e) inj ctx

-- | construct: Λ ε:⋆. λ p : (ε, listT ε) . roll (listT ε) (Inj Cons p (listSumT ε)) as α.(α ε)
consListVal :: Term
consListVal =
  let
    ve = s2n "ε"
    va = s2n "α"
    vp = s2n "p"
    e = TV ve
    a = TV va
    p = V vp
    pt = tupleT [e, listT `TApp` e]
    inj = Inj (FUser "Cons") p (listSumT `TApp` e)
    ctx = bind va (a `TApp` e)
  in PLam $ bind (ve, embed KType)
     $ Lam $ bind (vp, embed pt)
     $ Roll (listT `TApp` e) inj ctx
    
    
