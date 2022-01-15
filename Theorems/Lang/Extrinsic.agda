module Theorems.Lang.Extrinsic where

open import Lang.Extrinsic

-- Proving preservation, i.e. if t evaluates to t'
-- then t' has the same type as t:
preservation : ∀ {t t' τ} → t ⇒ t' → t ∷ τ → t' ∷ τ
-- 1) We have     t ⇒ t'
--          ------------------
--            succ t ⇒ succ t'
-- 2) We have   t ∷ nat
--          ----------------
--            succ t ∷ nat
-- From (1)  and (2), we can show by induction that t' ∷ nat. But, we whave
-- succ t ⇒ succ t' and the only rule that applies to succ it T-Succ, so we
-- conclude that succ t' ∷ nat.
preservation (E-Succ t⇒t') (T-Succ t∷nat) = T-Succ (preservation t⇒t' t∷nat)
-- 1) We have pred zero ⇒ zero
-- 2) We have   t ∷ nat
--          --------------
--           pred t ∷ nat
-- Thus, the only rule that applies is T-Zero.
preservation E-PredZero (T-Pred t∷nat) = T-Zero
-- 1) We have pred (succ n) ⇒ n
-- 2) We have   succ n ∷ nat
--         -----------------------
--           pred (succ n) ∷ nat
-- But, the only possible rule for succ n ∷ nat is T-Succ, so we also have
--     n ∷ nat
-- ----------------
--   succ n ∷ nat
-- and we are done, since from (1) we want to show that n ∷ nat.
preservation {t' = n} E-PredSucc (T-Pred (T-Succ n∷nat)) = n∷nat
-- 1) We have     t ⇒ t'
--          ------------------
--            pred t ⇒ pred t'
-- 2) We have   t ∷ nat
--          ----------------
--            pred t ∷ nat
-- From (1)  and (2), we can show by induction that t' ∷ nat. But, we whave
-- pred t ⇒ pred t' and the only rule that applies to pred it T-Pred so we
-- conclude that pred t' ∷ nat.
preservation (E-Pred t⇒t') (T-Pred t∷nat)
  = T-Pred (preservation t⇒t' t∷nat)
-- We have iszero zero ⇒ true and we want to show that true ∷ bool, which
-- follows directly from T-True.
preservation E-IsZeroZero (T-IsZero zero∷nat) = T-True
-- We have iszero (succ n) ⇒ false and we want to show that true ∷ bool,
-- which follows directly from T-False.
preservation E-IsZeroSucc (T-IsZero succ∷nat) = T-False
-- 1) We have       t ⇒ t'
--          ---------------------
--           iszero t ⇒ iszero t'
-- 2) We have    t∷nat
--         ------------------
--           iszero t ∷ nat
-- By induction, we know that t' ∷ nat. Thus, we can apply rule T-IsZero
-- to show that iszero t' ∷ bool.
preservation (E-IsZero t⇒t') (T-IsZero t∷nat)
  = T-IsZero (preservation t⇒t' t∷nat)
-- 1) We have if true then t₂ else t₃ ⇒ t₂
-- 2) We have  true ∷ bool    t₂ ∷ τ    t₃∷τ
--         -----------------------------------------
--               if true then t₂ else t₃ ∷ τ
-- We want to show that t₂ ∷ τ, which from (1) is the term that the
-- if expression evaluates to. Notice that we already have the proof
-- for t₂ ∷ τ from (2).
preservation {t' = t₂} E-IfTrue (T-If true∷bool t₂∷τ t₃∷τ) = t₂∷τ
-- 1) We have if false then t₂ else t₃ ⇒ t₃
-- 2) We have  false ∷ bool    t₂ ∷ τ    t₃∷τ
--         -----------------------------------------
--               if false then t₂ else t₃ ∷ τ
-- We want to show that t₃ ∷ τ, which from (1) is the term that the
-- if expression evaluates to. Notice that we already have the proof
-- for t₃ ∷ τ from (2).
preservation {t' = t₃} E-IfFalse (T-If false∷bool t₂∷τ t₃∷τ) = t₃∷τ
-- 1) We have                   t₁ ⇒ t₁'
--         -------------------------------------------------
--           if t₁ then t₂ else t₃ ⇒ if t₁' then t₂ else t₃
-- 2) We have   t₁ ∷ bool    t₂ ∷ τ    t₃∷τ
--         -----------------------------------------
--               if t₁ then t₂ else t₃ ∷ τ
-- From (1) we know that t₁ ⇒ t₁' and from (2) we know that t₁ ∷ bool,
-- t₂∷τ and t₃∷τ. We can apply induction to show that t₁' ∷ bool and
-- then use rule T-If to show that if t₁' then t₂ else t₃ ∷ τ.
preservation (E-If t₁⇒t₁') (T-If t₁∷bool t₂∷τ t₃∷τ)
  = T-If (preservation t₁⇒t₁' t₁∷bool) t₂∷τ t₃∷τ
