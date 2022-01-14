module Theorems.Data.Parity where

open import Data.Nat
open import Data.Parity
open import Theorems.Data.Nat

-- Proving that "m is even ∧ n is even ⇒ m + n is even".
+-evens : ∀ {m n} → Even m → Even n → Even (m + n)
-- 0 + n ≡ n and n is even:
+-evens zero even-n = even-n
-- Let m = suc (suc m'). We have the following steps:
-- 1) m is even, i.e.  suc (suc m') is even, so by induction m' is even.
-- 2) We canthen  apply induction on m' and n to conclude that
--    m' + n is even.
-- 3) Then, by the definition of Even, suc (suc (m' + n)) is even.
-- 4) We want to prove that m + n is even. By relying on the inductive
--    definition of "+", we have:
--      m + n              ≡
--      suc (suc m') + n   ≡
--      suc (suc m' + n)   ≡
--      suc (suc (m' + n)) ∎
--    Since, from step (3), suc (suc (m' + n)) is even, it follows that
--    m + n is even.
+-evens (suc even-m') even-n = suc (+-evens even-m' even-n)

-- Example:
even-2 : Even 2
even-2 = suc zero

even-0+2 : Even (0 + 2)
even-0+2 = +-evens zero even-2

-- The double of a number is even:
even-double : ∀ {n} → Even (n + n)
even-double {zero} = zero
-- By following the definition of +, we have the following equality:
--   n + n             ≡
--   suc n' + suc n'   ≡
--   suc (n' + suc n') ∎
-- Notice that, by the definition of +, which applies induction only on the
-- left argument, Agda cannot reduce further the last expression above. Thus,
-- we need to rely on the commutative property of addition:
--   suc (n' + suc n')   ≡
--   suc (suc n' + n')   ≡
--   suc (suc (n' + n')) ∎
-- Finally, by induction we have that n' + n' is even. Thus, we just need
-- to use the constructor "suc" of Even.
even-double {suc n'} rewrite +-comm {n'} {suc n'} = suc (even-double {n'})
