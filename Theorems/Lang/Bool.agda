module Theorems.Lang.Bool where

open import Lang.Bool
open import Agda.Builtin.Equality

-- Proving that that the if term "commutes":
if-comm : ∀ {t₁ t₂ t₃}
        → eval (if t₁ then t₂ else t₃) ≡ eval (if (not t₁) then t₃ else t₂)
if-comm {t₁} with eval t₁
-- Step by step:
--   eval (if t₁ then t₂ else t₃)   ≡
--   eval (if true then t₂ else t₃) ≡
--   eval t₂                        ∎
-- and
--   eval (if (not t₁) then t₃ else t₂)   ≡
--   eval (if (not true) then t₃ else t₂) ≡
--   eval (if false then t₃ else t₂)      ≡
--   eval t₂                              ∎
... | true  = refl
-- Step by step:
--   eval (if t₁ then t₂ else t₃)    ≡
--   eval (if false then t₂ else t₃) ≡
--   eval t₃                         ∎
-- and
--   eval (if (not t₁) then t₃ else t₂)    ≡
--   eval (if (not false) then t₃ else t₂) ≡
--   eval (if true then t₃ else t₂)        ≡
--   eval t₃                               ∎
... | false = refl
