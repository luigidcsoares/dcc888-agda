module Theorems.Data.Nat where

open import Data.Nat
open import Agda.Builtin.Equality

-- Proving that n + zero reduces to n:
+-zero-right : ∀ {n} → n + 0 ≡ n
+-zero-right {zero} = refl
-- We have n ≡ suc n' and we initially want to show that
-- suc n' + zero ≡ suc n'. By the definition of +, we have
--   suc n' + zero   ≡
--   suc (n' + zero) ∎
-- and, by induction, we have that n' + zero ≡ n. We are relying
-- on the "rewrite" mechanism of Agda so that we can replace n' + zero
-- with n' in the expression suc (n' + zero). After that, we now need
-- to show that suc n' ≡ suc n', which follows from refl.
+-zero-right {suc n'} rewrite +-zero-right {n'} = refl

-- Proving that suc (m + n) ≡ m + suc n:
+-suc : ∀ {m n} → suc (m + n) ≡ m + suc n
+-suc {zero} = refl
+-suc {suc m'} {n} rewrite +-suc {m'} {n} = refl

-- Proving commutativity for addition:
+-comm : ∀ {m n} → m + n ≡ n + m
+-comm {zero} {n} rewrite +-zero-right {n} = refl
+-comm {suc m'} {n} rewrite +-comm {m'} {n} | +-suc {n} {m'} = refl
