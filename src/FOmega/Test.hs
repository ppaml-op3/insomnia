{-# LANGUAGE OverloadedStrings #-}
module FOmega.Test where

import qualified Data.Text as T

import FOmega.Parse
import FOmega.Check
import qualified Text.Parsec (parse)
import Insomnia.Pretty (Pretty, ppDefault)

-- | Parsing playground - types
-- >>> playType "forall a : * . exists c : * -> * . c a -> c (a -> a) -> c a "
-- ∀ a ∷ ⋆ . ∃ c ∷ ⋆ → ⋆ . c a → c (a → a) → c a
-- ⋆
-- >>> playType "forall a : * . forall c : * -> * -> * . c a -> c (a -> a) -> c a "
-- ∀ a ∷ ⋆ . ∀ c ∷ ⋆ → ⋆ → ⋆ . c a → c (a → a) → c a
-- ExpectedKType (TApp (TV c) (TV a)) (Got {unGot = KArr KType KType})
-- *** Exception: user error (Did not kindcheck.)
playType :: T.Text -> IO ()
playType = play typeExpr inferK

-- | Parsing playground - terms
-- >>> playTerm "λ [a : *] [c : * -> *] (x : (λ w : * . c w) a -> a) (y : c ((λ t : * . t) a)). x y"
-- λ [a ∷ ⋆]
--   . λ [c ∷ ⋆ → ⋆]
--       . λ (x ∷ (λ w ∷ ⋆ . c w) a → a) . λ (y ∷ c ((λ t ∷ ⋆ . t) a)) . x y
-- ∀ a ∷ ⋆
--   . ∀ c ∷ ⋆ → ⋆ . ((λ w ∷ ⋆ . c w) a → a) → c ((λ t ∷ ⋆ . t) a) → a

playTerm :: T.Text -> IO ()
playTerm = play termExpr inferTy

play :: (Pretty a, Pretty b) => Parser a -> (a -> TC IO b) -> T.Text -> IO ()
play parseIt checkIt txt = do
  let p = Text.Parsec.parse parseIt "-" txt
  t <- case p of
   Left err -> do
     print err
     fail "No parse."
   Right t -> do
     print (ppDefault t)
     return t
  ans <- runTC $ checkIt t
  case ans of
   Left err -> do
     print err
     fail "Did not check."
   Right k ->
     print (ppDefault k)

