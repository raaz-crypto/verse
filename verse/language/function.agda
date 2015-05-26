module verse.language.function where

open import Data.List
open import Data.Nat
open import Data.Product        using (_×_)
open import Data.String
open import Data.Unit           using (⊤)

open import verse.error
open import verse.language.arch
open import verse.language.types

open Arch

infixr 4 _,_
infix  5 ● ○

{--
infixr 2 _×_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y
--}


Typeⁿ : ℕ → Set
Typeⁿ zero        = ⊤
Typeⁿ (suc zero)    = {d : Dim}{k : Kind {d} ✓} → Type k
Typeⁿ (suc (suc n)) = ({d : Dim}{k : Kind {d} ✓} → Type k) × Typeⁿ (suc n)


data OpType : Set where
  param : OpType
  local : OpType


data Op : Set where
  ● : OpType → {d : Dim}{k : Kind {d} ✓} → Type k → Op
  ○ : OpType → {d : Dim}{k : Kind {d} ✓} → Type k → Op


data ArgDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _,_  : {n : ℕ} → Op → ArgDecl {n} (Typeⁿ n) → ArgDecl {suc n} (Typeⁿ (suc n))


funcType : Arch → {n : ℕ} → ArgDecl {n} (Typeⁿ n) → Set
funcType arch void          = List (instruction arch)
funcType arch (● param ty , rest) = Parameter arch ReadWrite ty → funcType arch rest
funcType arch (○ param ty , rest) = Parameter arch ReadOnly ty → funcType arch rest
funcType arch (● local ty , rest) = Local arch ReadWrite ty → funcType arch rest
funcType arch (○ local ty , rest) = Local arch ReadOnly ty → funcType arch rest

data FuncDecl (arch : Arch) : Set where
  function : {n : ℕ} → String → (args : ArgDecl {n} (Typeⁿ n)) → (f : funcType arch args) → FuncDecl arch
