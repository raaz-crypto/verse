module verse.product where

open import Data.Nat

open import Level using (Level)
record _×_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  constructor _,_
  field
    proj₀ : A
    proj₁ : B

data ⊤ {ℓ : Level} : Set ℓ where
     tt : ⊤

_^_ : {ℓ : Level}(A : Set ℓ) → ℕ → Set ℓ
A ^ 0       = ⊤
A ^ 1       = A
A ^ (suc m) = A × A ^ m

infixr 0 _×_
infixr 0 _,_
infixr 7 _^_

-- Map on Aⁿ.
map : ∀{n}{ℓ : Level}{A B : Set ℓ}
    → (A → B) → A ^ n → B ^ n
map {0}           _ tt       = tt
map {1}           f x        = f x
map {suc (suc n)} f (x , xs) = f x , map {suc n} f xs

-- Fold Aⁿ from the right.
foldr :  ∀{n}
      → {ℓ : Level}{A B : Set ℓ}
      → (A → B → B) → B → A ^ n → B
foldr {0}           f b  tt      = b
foldr {1}           f b  x       = f x b
foldr {suc (suc n)} f b (x , xs) = f x (foldr {suc n} f b xs)

-- Fold Aⁿ from the left.
foldl :  ∀{n}
      → {ℓ : Level}   {A B : Set ℓ}
      → (B → A → B) → B → A ^ n  → B
foldl {0}           f b  tt      = b
foldl {1}           f b  x       = f b x
foldl {suc (suc n)} f b (x , xs) = foldl {suc n} f (f b x) xs


zipWith : ∀{n} {a b c : Set} → (a → b → c) → a ^ n → b ^ n → c ^ n
zipWith {0}           _ tt        tt        =  tt
zipWith {1}           f a         b         =  f a b
zipWith {suc (suc n)} f (a₀ , aˢ) (b₀ , bˢ)
        =  f a₀ b₀ , zipWith {suc n} f aˢ bˢ

_ˢ : ∀{n}{A : Set} → A → A ^ (suc n)
_ˢ {0}     a = a
_ˢ {suc n} a = a , _ˢ {n} a
