module verse.product where

open import Data.Bool
open import Data.Product        public
                                using    ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit           using    ( ⊤ )
open import Data.Nat            hiding   ( _⊔_ )
                                renaming ( _≤_  to _≤ℕ_ 
                                         ; _≤?_ to _≤?ℕ_
                                         ; _≟_  to _≟ℕ_
                                         )
open import Function
open import Level               hiding   (suc)
open import Relation.Binary
open import Relation.Nullary

open import verse.error


ℕⁿ : {n : ℕ} → Set
ℕⁿ {zero}        = ⊤
ℕⁿ {suc zero}    = ℕ
ℕⁿ {suc (suc n)} = ℕ × ℕⁿ {suc n}


-- ℕⁿ equality predicate
_≟ℕⁿ_ : {n₁ n₂ : ℕ} → ℕⁿ {n₁} → ℕⁿ {n₂} → Bool
_≟ℕⁿ_ {zero}  {zero}  _ _ = true
_≟ℕⁿ_ {zero}  {suc n} _ _ = false
_≟ℕⁿ_ {suc n} {zero}  _ _ = false
_≟ℕⁿ_ {suc zero} {suc zero} x y = is x ≟ℕ y Provable
_≟ℕⁿ_ {suc zero}    {suc (suc n)} _ _ = false
_≟ℕⁿ_ {suc (suc n)} {suc zero}    _ _ = false
_≟ℕⁿ_ {suc (suc n₁)} {suc (suc n₂)} (x , xs) (y , ys) = ifProvable x ≟ℕ y Then (xs ≟ℕⁿ ys)


_≤_ : ∀{n : ℕ} → ℕⁿ {suc n} → ℕⁿ {suc n} → Set
_≤_ {zero} a b = a ≤ℕ b
_≤_ {suc n} (a , as) (b , bs) = a ≤ℕ b  ×  as ≤ bs


_≤?_ : ∀{n} → Decidable (_≤_ {n})
_≤?_ {zero}  a        b        = a ≤?ℕ b
_≤?_ {suc n} (a , as) (b , bs)
     with a ≤?ℕ b | as  ≤? bs
...  |    yes p   | yes q    = yes (p , q)
...  |    no  neg | _        = no (neg ∘ proj₁)
...  |    _       | no neg   = no (neg ∘ proj₂)


-- a ˢ is a , a , .... n times.
_ˢ : {n : ℕ} → ℕ → ℕⁿ {suc n}
_ˢ {0}     a = a
_ˢ {suc n} a = a , a ˢ
