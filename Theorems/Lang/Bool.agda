module Theorems.Lang.Bool where

open import Lang.Bool

-- Proving that that the if term "commutes":
if-comm : ∀ {t₁ t₂ t₃ v} → (if t₁ then t₂ else t₃) ⇓ v
                         → (if (not t₁) then t₃ else t₂) ⇓ v
if-comm (B-True  t₁⇓true  t₂⇓v) = B-False (B-NotTrue t₁⇓true) t₂⇓v
if-comm (B-False t₁⇓false t₃⇓v) = B-True (B-NotFalse t₁⇓false) t₃⇓v
