module Data.Nat where

open import Agda.Builtin.Equality

-- Definition of natural numbers following Peano's axioms:
-- Base case: zero is a natural number
-- Induction step:   n is natural
--                ------------------
--                 suc n is natural

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Addition can also be defined by induction:
-- Base case: 0 + n = n
-- Induction step:      m + n = k
--                --------------------
--                  suc m + n = suc k

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- Let's check if it works:
1+2≡3 : 1 + 2 ≡ 3
1+2≡3 = refl

-- refl (reflexivity) is the unique constructor for equality.
-- Equality is defined as follows:
--
--   data _≡_ {a} {A : Set a} (x : A) : A → Set a where
--     refl : x ≡ x
--
-- Step by step proof for 1+2≡3, following the definition of "+":
--   1 + 2                       ≡
--   suc zero + suc (suc zero)   ≡
--   suc (zero + suc (suc zero)) ≡
--   suc (suc (suc zero))        ≡
--   3                           ∎

-- Let's also define - and *:
-- For subtraction, we have two base cases:
-- Base case 1: m - 0 = m
-- Base case 2: 0 - suc n = 0 (recall that we are defining natural numbers,
--                             so we don't have negative numbers.)
-- Induction step:     m - n = k
--                --------------------
--                 suc m - suc n = k

infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
m     - zero  = m
zero  - suc n = zero
suc m - suc n = m - n

-- Multiplication can be defined as follows:
-- Base case: 0 * n = 0
-- Induction step:    n + m * n = k
--                 --------------------
--                    suc m * n = k

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n
