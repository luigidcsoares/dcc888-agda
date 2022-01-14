module Lang.Bool where

data Val : Set where
  true false : Val

data Term : Set where
  const         : Val → Term
  not           : Term → Term
  if_then_else_ : Term → Term → Term → Term

-- Big step semantics:
eval : Term → Val
eval (const x) = x
eval (not t) with eval t
... | true  = false
... | false = true
eval (if t₁ then t₂ else t₃) with eval t₁
... | true  = eval t₂
... | false = eval t₃
