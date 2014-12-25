module verse.product where

import Data.Product
open        Data.Product public
-- open        Data.Product public using    ( proj₁; proj₂ )
open import Data.Unit           using    ( ⊤ )
open import Data.Nat            hiding   ( _⊔_ )
                                renaming ( _≤_ to _≤ℕ_; _≤?_ to _≤?ℕ_ )

open import Function
open import Level               hiding   (suc)

open import Relation.Binary
open import Relation.Nullary


ℕⁿ : {n : ℕ} → Set
ℕⁿ {zero}        = ⊤
ℕⁿ {suc zero}    = ℕ
ℕⁿ {suc (suc n)} = ℕ × ℕⁿ {suc n}

_≤_ : ∀{n : ℕ} → ℕⁿ {suc n} → ℕⁿ {suc n} → Set
_≤_ {ℕ.zero} a b = a ≤ℕ b
_≤_ {suc n} (a , as) (b , bs) = a ≤ℕ b  ×  as ≤ bs

_≤?_ : ∀{n} → Decidable (_≤_ {n})
_≤?_ {0}     a        b        = a ≤?ℕ b
_≤?_ {suc n} (a , as) (b , bs)
     with a ≤?ℕ b | as  ≤? bs
...  |    yes p   | yes q    = yes (p , q)
...  |    no  neg | _        = no (neg ∘ proj₁)
...  |    _       | no neg   = no (neg ∘ proj₂)


-- a ˢ is a , a , .... n times.
_ˢ : {n : ℕ} → ℕ → ℕⁿ {suc n}
_ˢ {0}     a = a
_ˢ {suc n} a = a , a ˢ
