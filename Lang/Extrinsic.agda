module Lang.Extrinsic where

data Type : Set where
  bool nat : Type

data Term : Set where
  zero   : Term
  true   : Term
  false  : Term
  succ   : Term → Term
  pred   : Term → Term
  iszero : Term → Term
  if_then_else_ : Term → Term → Term → Term

-- Small step semantics:
data _⇒_ : Term → Term → Set where
  E-Succ : ∀ {t t'} →      t ⇒ t'
                    ----------------------
                    → succ t ⇒ succ t'
  E-PredZero : pred zero ⇒ zero
  E-PredSucc : ∀ {n} → pred (succ n) ⇒ n
  E-Pred : ∀ {t t'} →      t ⇒ t'
                    ------------------------
                    → pred t ⇒ pred t'
  E-IsZeroZero : iszero zero ⇒ true
  E-IsZeroSucc : ∀ {n} → iszero (succ n) ⇒ false
  E-IsZero : ∀ {t t'} →        t ⇒ t'
                      ----------------------
                      → iszero t ⇒ iszero t'
  E-IfTrue  : ∀ {t₂ t₃} → (if true then t₂ else t₃) ⇒ t₂
  E-IfFalse : ∀ {t₂ t₃} → (if false then t₂ else t₃) ⇒ t₃
  E-If : ∀ {t₁ t₁' t₂ t₃} →         t₁ ⇒ t₁'
                          ----------------------------
                          → (if t₁ then t₂ else t₃) ⇒
                            (if t₁' then t₂ else t₃)

-- Type system:
data _∷_ : Term → Type → Set where
  T-True  : true ∷ bool
  T-False : false ∷ bool
  T-If : ∀ {t₁ t₂ t₃ τ} → t₁ ∷ bool → t₂ ∷ τ → t₃ ∷ τ
                        -------------------------------
                        → (if t₁ then t₂ else t₃) ∷ τ
  T-Zero : zero ∷ nat
  T-Succ : ∀ {t} →    t ∷ nat
                 -----------------
                 → succ t ∷ nat
  T-Pred : ∀ {t} →    t ∷ nat
                 -----------------
                 → pred t ∷ nat
  T-IsZero : ∀ {t} →     t ∷ nat
                   ------------------
                   → iszero t ∷ bool
