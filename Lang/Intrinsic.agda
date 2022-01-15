module Lang.Intrinsic where

open import Agda.Builtin.Bool
open import Data.Nat
open import Data.Relation

data Type : Set where
  bool nat : Type

data Term : Type → Set where
  zero   : Term nat
  true   : Term bool
  false  : Term bool
  succ   : Term nat → Term nat
  pred   : Term nat → Term nat
  iszero : Term nat → Term bool
  if_then_else_ : ∀ {τ} → Term bool → Term τ → Term τ → Term τ

⟦_⟧T : Type → Set
⟦ nat ⟧T  = ℕ
⟦ bool ⟧T = Bool

eval : ∀ {τ} → Term τ → ⟦ τ ⟧T
-- If we hadn't embedded the type τ into the term, we'd have multiple cases
-- according to τ. For instance, we'd have:
--   eval {τ = nat}  zero = 0
--   eval {τ = bool} zero = ?
eval zero = 0
eval true = true
eval false = false
eval (succ t) = eval t + 1
eval (pred t) = eval t - 1
eval (iszero t) = eval t ≡ᵇ 0
eval (if t₁ then t₂ else t₃) with eval t₁
... | true  = eval t₂
... | false = eval t₃
