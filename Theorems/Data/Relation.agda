module Theorems.Data.Relation where

open import Data.Nat
open import Data.Relation

-- Proving that "m > n ⇒ n ≤ m":
>-inv : ∀ {m n} → m > n → n ≤ n
-- We have m ≡ suc k and n ≡ zero. Since zero ≤ any number,
-- we can just use the constructor zero of ≤ relation:
>-inv zero = zero
-- We have m ≡ suc m', n ≡ suc n' and suc m' > suc n', which,
-- by the definition of constructor "suc" of >, means that
-- m' > n. By induction on m' > n', we have that n' ≤ m'. Thus,
-- via constructor suc of ≤, we have suc n' ≤ suc m ≡ n ≤ m.
>-inv (suc m'>n') = suc (>-inv m'>n')
