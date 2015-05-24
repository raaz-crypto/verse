module verse.arch.c.c-instructions where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_)

open import verse.arch.c.c-arch
open import verse.error
open import verse.language.arch
open import verse.language.types
open import verse.language.instructions


-- instances of ToCvar for Data Types Parameter, Register and Local

private
  module OperandToCvar {d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access} where

    instance
      paramToCvar : ToCvar (Parameter c-arch acc ty)
      paramToCvar = record { toCvar = helper }
        where helper : Parameter c-arch acc ty → CVariable
              helper (param x) = x

      regToCvar : ToCvar (Register c-arch acc ty)
      regToCvar = record { toCvar = helper}
        where helper : Register c-arch acc ty → CVariable
              helper (reg x) = x

      localToCvar : ToCvar (Local c-arch acc ty)
      localToCvar = record { toCvar = helper}
        where helper : Local c-arch acc ty → CVariable
              helper (localStack x) = x
              helper (localReg x) = x

open OperandToCvar public


-- instances of AddEq for c-architecture

open Operand
open ToCvar ⦃...⦄
open AddEq

instance
  cAddEq : {d : Dim}{k : Kind {d} ✓}{A B : Set}
         → ⦃ A'' : ToCvar A ⦄ ⦃ B'' : ToCvar B ⦄
         → ⦃ A' : Operand A ⦄ ⦃ B' : Operand B ⦄
         → ⦃ typeEq : typeOf? A' ≡ typeOf? B' ⦄
         → ⦃ accEq  : access? A' ≡ ReadWrite ⦄
         → AddEq {c-arch}{d}{k} A B
  cAddEq ⦃ typeEq = typeEq ⦄ ⦃ accEq = accEq ⦄ = record { accAEq = accEq
                                                         ; typeEq = typeEq
                                                         ; _+≔_ = λ op₁ op₂ → [ toCvar op₁ +≐ toCvar op₂ ]
                                                         }
