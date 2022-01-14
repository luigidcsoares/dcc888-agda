module Data.Parity where

open import Data.Nat

-- Even numbers can be defined as follows:
-- Base case: 0 is even
-- Induction step:      n is even
--                ---------------------
--                 suc (suc n) is even

data Even : ℕ → Set where
  -- Notice that the first "zero" is a constructor for even numbers,
  -- whereas the second zero is the natural number zero. The same
  -- applies to the constructor "suc".
  zero : Even zero
  -- "n" is an implicit argument.
  suc  : ∀ {n} → Even n → Even (suc (suc n))

-- Odd numbers can be defines in a similar way:
-- Base case: 1 is odd
-- Induction step:      n is odd
--                ---------------------
--                 suc (suc n) is odd

data Odd : ℕ → Set where
  zero : Odd 1
  suc  : ∀ {n} → Odd n → Odd (suc (suc n))
