module Lang.Bool where

data Term : Set where
  true  : Term
  false : Term
  not   : Term → Term
  if_then_else_ : Term → Term → Term → Term

-- Big step semantics:
data _⇓_ : Term → Term → Set where
  B-True  : ∀ {t₁ t₂ t₃ v} →      t₁ ⇓ true → t₂ ⇓ v
                           --------------------------------
                           → (if t₁ then t₂ else t₃) ⇓ v
  B-False : ∀ {t₁ t₂ t₃ v} →      t₁ ⇓ false → t₃ ⇓ v
                           --------------------------------
                           → (if t₁ then t₂ else t₃) ⇓ v
  B-NotTrue  : ∀ {t} →   t ⇓ true
                    -------------------
                     → not t ⇓ false
  B-NotFalse : ∀ {t} →   t ⇓ false
                    -------------------
                     → not t ⇓ true
