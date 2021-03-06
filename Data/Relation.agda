module Data.Relation where

open import Agda.Builtin.Bool
open import Data.Nat

-- Definition of ≤ relation:
-- Base case: 0 ≤ n
-- Induction step:     m ≤ n
--                ---------------
--                 suc m ≤ suc n

infix 4 _≤_
data _≤_ : ℕ → ℕ → Set where
  zero : ∀ {n} → zero ≤ n
  suc  : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- Definition of > relation:
-- Base case: suc n > 0
-- Induction step:     m > n
--                ---------------
--                 suc m > suc n

infix 4 _>_
data _>_ : ℕ → ℕ → Set where
  zero : ∀ {n} → suc n > zero
  suc  : ∀ {m n} → m > n → suc m > suc n

-- Boolean equivalence for natural numbers:
_≡ᵇ_ : ℕ → ℕ → Bool
zero  ≡ᵇ zero  = true
zero  ≡ᵇ suc n = false
suc m ≡ᵇ zero  = false
suc m ≡ᵇ suc n = m ≡ᵇ n
