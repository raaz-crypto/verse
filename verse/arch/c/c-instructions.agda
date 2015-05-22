module verse.arch.c.c-instructions where

open import verse.error
open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import verse.arch.c.c-arch
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

-- instances of ToCvar for Data Types Parameter, Register and Local

instance
  paramToCvar : {d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access} → ToCvar (Parameter c-arch acc ty)
  paramToCvar {ty = ty}{acc = acc} = record { toCvar = helper }
    where helper : Parameter c-arch acc ty → CVariable
          helper (param x) = x


{-
private
  module OperandToCvar {d : Dim}{k : Kind {d} ✓}{ty : Type k} where

    regToCvar : {acc : Access}{ty : Type k} → ToCvar (Register c-arch)
    regToCvar = record { toCvar = helper}
      where helper : {acc : Access}{ty : Type k}(a : Register c-arch acc ty) → CVariable
            helper (reg _ x) = x

    localToCvar : {acc : Access}{ty : Type k} → ToCvar (Local c-arch)
    localToCvar = record { toCvar = helper}
      where helper : {acc : Access}{ty : Type k}(a : Local c-arch acc ty) → CVariable
            helper (localStack _ x) = x
            helper (localReg _ x) = x


open OperandToCvar public
-}


-- instances of AddEq for c-architecture

{-

record AddEq {arch : Arch}{d : Dim}{k : Kind {d} ✓}(A B : Set) {{ A' : Operand {arch}{d}{k} A }} {{ B' : Operand {arch}{d}{k} B }} : Set where
  field
    _+≔_   : A → B → List (instruction arch)
    typeOf : {a : A}{b : B} → typeOf? a ≡ typeOf? b
    accOfA : {a : A} → access? a ≡ ReadWrite

-}

open Operand {{...}}
open ToCvar {{...}}

instance
  cAddEq : {d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access}{A B : Set}
         → {{ A'' : ToCvar A }} {{ B'' : ToCvar B }}
         → {{ A' : Operand {c-arch}{d}{k}{ty}{ReadWrite} A }} {{ B' : Operand {c-arch}{d}{k}{ty}{acc} B }}
         → AddEq {arch = c-arch} A B
  cAddEq = record { _+≔_ = λ op₁ op₂ → [ toCvar op₁ +≐ toCvar op₂ ]
                  }
         


{-

instance cAddEq : {d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access}
                → {A B : Access → Type k → Set} ⦃ A' : ToCvar (A ReadWrite ty) ⦄ ⦃ B' : ToCvar (B acc ty) ⦄
                → AddEq {arch = c-arch}{d = d}{k = k} ty A B
         cAddEq = record { _+≔_  = λ op₁ op₂ → [ toCvar op₁ CInstruction.+≔ toCvar op₂ ]}

cAddEq ⦃ A' ⦄ ⦃ B' ⦄ = record { _+≔_ = helper A' B'}
  where helper : {d : Dim}{k : Kind {d} ✓}{A B : Access → Type k → Set}
               → (A' : ToCvar A)(B' : ToCvar B)
               → {acc : Access} {ty : Type k}
               → A ReadWrite ty → B acc ty → List (instruction c-arch)
        helper op₁ op₂ = [ (toCvar op₁) CInstruction.+≔ (toCvar op₂) ]

-}
