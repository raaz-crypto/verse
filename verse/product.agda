module verse.product where

import Data.Product
open        Data.Product        renaming ( _×_ to _⊗_)
open        Data.Product public using    (_,_; proj₁; proj₂ )
open import Data.Unit           using    ( ⊤ )
open import Data.Nat            hiding   ( _⊔_ )
open import Level               hiding   (suc)


_×_ : {a b : Level} → Set a → Set b → Set (a ⊔ b)
abstract A × B = A ⊗ B
infixr 2 _×_

ℕⁿ : {n : ℕ} → Set
ℕⁿ {zero}        = ⊤
ℕⁿ {suc zero}    = ℕ
ℕⁿ {suc (suc x)} = ℕ × ℕⁿ {suc x}
