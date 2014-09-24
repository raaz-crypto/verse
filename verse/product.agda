module verse.product where

open import Level
record _×_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    proj₀ : A
    proj₁ : B

infixr 0 _×_
infixr 0 _,_
