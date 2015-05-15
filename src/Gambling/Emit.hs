{-# LANGUAGE FlexibleInstances #-}
module Gambling.Emit where

import Data.Monoid

import Data.Format

import qualified Text.PrettyPrint as PP

import qualified Control.Monad.State.Lazy as LazySt

import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.LocallyNameless.Operations (lunbind, unrec, unembed, unrebind)
import Unbound.Generics.LocallyNameless (Name, name2String)

import Gambling.Racket

-- | Emitter monad stack
type EmitM = LazySt.StateT EmitState LFreshM

-- | An emitter is a final encoding of a state machine that accepts
-- some number of document fragments and yields a document fragment.
data Emitter = Emitter {
  emitMore :: PP.Doc -> Emitter
  , emitDone :: PP.Doc
  }

-- | The emitter state is a stack of emitters where the ones at the
-- head of the list will be fed to the ones in the tail once they are
-- done.
newtype EmitState = EmitState [Emitter]

-- | Accumulate all the fragments using (<>)
emitFrom :: PP.Doc -> Emitter
emitFrom initial = Emitter (\more -> emitFrom (initial <> more)) initial

-- | Accept a single fragment, transform it, and refuse to accept any more.
emitOne :: (PP.Doc -> PP.Doc) -> Emitter
emitOne xform = Emitter (\t -> emitZero (xform t)) (error "Gambling.Emit.emitOne:  internal error, called done without emitting anything")

-- | Don't accept any more input and just yield the given fragment.
emitZero :: PP.Doc -> Emitter
emitZero d = Emitter (\_ -> error "Gambling.Emit.emitZero: internal error, called with more outputput when expecting to be done") d

-- | Accumulate a collection of fragments and collapse them into a
-- single fragment using the given function.
emitCollection :: ([PP.Doc] -> PP.Doc) -> Emitter
emitCollection collapse = go id
  where
    go k = Emitter (\d -> go (\ds -> k (d:ds))) (collapse (k []))

-- | Collapse a collection of fragments using paragraph fill.
emitFSep :: Emitter
emitFSep = emitCollection PP.fsep

-- | Collapse a collection of fragments using vertical catenation.
emitVCat :: Emitter
emitVCat = emitCollection PP.vcat

-- | Run the emitter monad.
emitIt :: Emit e => e -> Doc
emitIt e = h $ runLFreshM $ LazySt.execStateT (emit e) (EmitState [initialEmitter])
  where
    initialEmitter = emitFrom mempty
    h (EmitState []) = error "Gambling.Emit.emitIt: internal error, unexpected empty emitter stack"
    h (EmitState [em]) = format $ emitDone em
    h (EmitState (em:em':ems)) = h (EmitState (emitMore em' (emitDone em) : ems))

-- | Push a new emitter onto the emitter stack
pushEmitter :: Emitter -> EmitM ()
pushEmitter emitter = LazySt.modify h
  where
    h (EmitState rest) = EmitState $ emitter:rest

-- | Inform the top emitter that it is done, pop it off the stack and
-- feed the fragment that it yeilds to the next emitter on the stack.
done :: EmitM ()
done = LazySt.modify h
  where
    h (EmitState (e:e':rest)) = EmitState (emitMore e' (emitDone e) : rest)
    h (EmitState _) = error "internal error: Gambling.Emit.done emitter stack of < 2 elements"

-- | emittable things
class Emit e where
  emit :: e -> EmitM ()

instance Emit PP.Doc where
  emit b = LazySt.modify h
    where
      h (EmitState []) = error "internal error: Gambling.Emit.emit PP.Doc emitter stack is empty"
      h (EmitState (e:rest)) = EmitState (emitMore e b : rest)

instance Emit [Char] where
  emit = emit . PP.text


instance Emit (Name a) where
  emit = emit . name2String

parens, brackets :: EmitM a -> EmitM a
parens = enclosing PP.parens
brackets = enclosing PP.brackets

nesting :: Emitter -> EmitM a -> EmitM a
nesting emitter m = do
  pushEmitter emitter
  a <- m
  done
  return a

enclosing :: (PP.Doc -> PP.Doc) -> EmitM a -> EmitM a
enclosing wrap m = do
  nesting (emitOne wrap) $ nesting emitFSep $ m

instance Emit Expr where
  emit (Var v) = emit v
  emit (App es) = parens $ mapM_ emit es
  emit (Lam b) = parens $ lunbind b $ \(vs, body) -> do
    emit "lambda"
    parens $ mapM_ emit vs
    emit body
  emit (Let b) = parens $ lunbind b $ \(binds, body) -> do
    emit "let"
    parens $ mapM_ emit binds
    emit body
  emit (LetRec b) = parens $ lunbind b $ \(recBinds, body) -> do
    emit "letrec"
    parens $ mapM_ emit (unrec recBinds)
    emit body
  

instance Emit Binding where
  emit (Binding v e) = brackets $ do
    emit v
    emit (unembed e)

instance Emit Body where
  emit (Body bnd) = nesting emitVCat $ lunbind bnd $ \(recDefs, e) -> do
    let intDefs = unrec recDefs
    mapM_ emit intDefs
    emit e

instance Emit InternalDefn where
  emit (DefnID d) = emit d
  emit (ExprID e) = emit (unembed e)

instance Emit Definition where
  emit (Define rbnd) = parens $ do
    let (v, e) = unrebind rbnd
    emit "define"
    emit v
    emit (unembed e)

instance Emit Module where
  emit (Module modId modLang modDefns) = parens $ do
    emit "module"
    emit modId
    emit modLang
    emit modDefns

instance Emit ModuleDefnCtx where
  emit (ModuleDefnCtx bnd) = nesting emitVCat $ lunbind bnd $ \(recDefs, provides) -> do
    emit provides
    mapM_ emit (unrec recDefs)

instance Emit Provides where
  emit (Provides vs) = parens $ do
    emit "provide"
    mapM_ emit vs
  emit ProvidesAll = parens $ do
    emit "provide"
    parens $ emit "all-defined-out"

instance Emit ModuleBinding where
  emit (DefnMB d) = emit d
  emit (ExprMB e) = emit (unembed e)
  emit (RequireMB reqs) = emit reqs

instance Emit Requires where
  emit (Requires modPath vs) = parens $ do
    emit "require"
    parens $ do
      emit "only-in"
      emit (unembed modPath)
      mapM_ emit vs
    
    
