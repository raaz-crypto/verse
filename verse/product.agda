module verse.product where

open import Data.Nat
open import Data.Empty

open import Level using (Level)
record _×_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    proj₀ : A
    proj₁ : B

_^_ : (A : Set) → ℕ → Set
A ^ 0       = ⊥
A ^ 1       = A
A ^ (suc m) = A × A ^ m

infixr 0 _×_
infixr 0 _,_
infixr 7 _^_
