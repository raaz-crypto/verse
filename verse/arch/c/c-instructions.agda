module verse.arch.c.c-instructions where

open import Data.List
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import verse.arch.c.c-arch
open import verse.language.arch
open import verse.language.function
open import verse.language.machine
open import verse.language.instructions
open import verse.language.types
open import verse.language.userError


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


-- instance of AddEq for c-architecture

open Operand
open ToCvar ⦃...⦄
open AddEq

{-
instance
  cAddEq : {d : Dim}{k : Kind {d} ✓}{A B : Set}
         → ⦃ A'' : ToCvar A ⦄ ⦃ B'' : ToCvar B ⦄
         → ⦃ A' : Operand A ⦄ ⦃ B' : Operand B ⦄
         → ⦃ typeEq : typeOf? A' ≡ typeOf? B' ⦄
         → ⦃ accEq  : access? A' ≡ ReadWrite ⦄
         → ⦃ tyChkA' : CType? (typeOf? A') ≡ ✓ ⦄
         → AddEq {c-arch}{c-mach}{d}{k} A B
  cAddEq ⦃ A' = A' ⦄ ⦃ typeEq = typeEq ⦄ ⦃ accEq = accEq ⦄ = record { accAEq = accEq
                                                                      ; typeEq = typeEq
                                                                      ; _←+_   = helper
                                                                      }
    where helper : {d : Dim}{k : Kind {d} ✓}{A B : Set}
                 → ⦃ A'' : ToCvar A ⦄ ⦃ B'' : ToCvar B ⦄
                 → ⦃ A' : Operand {d}{k} A ⦄ ⦃ B' : Operand {d}{k} B ⦄
                 → A → B → Statement c-mach
          helper op₁ op₂ = ⟪ [ toCvar op₁ +≔ toCvar op₂ ] ,  ✓ ⟫
-}

instance
  cAddEq : {d : Dim}{k : Kind {d} ✓}{A B : Set}
         → ⦃ A'' : ToCvar A ⦄ ⦃ B'' : ToCvar B ⦄
         → ⦃ A' : Operand A ⦄ ⦃ B' : Operand B ⦄
         → ⦃ typeEq : typeOf? A' ≡ typeOf? B' ⦄
--         → ⦃ accEq  : access? A' ≡ ReadWrite ⦄
--         → ⦃ tyChkA' : CType? (typeOf? A') ≡ ✓ ⦄
         → AddEq {c-arch}{c-mach}{d}{k} A B
  cAddEq ⦃ A' = A' ⦄ ⦃ B' = B' ⦄ ⦃ typeEq = typeEq ⦄ = record { typeEq = typeEq
                                                    ; _←+_   = helper
                                                    }
    where helper : {d : Dim}{k : Kind {d} ✓}{A B : Set}
                 → ⦃ A'' : ToCvar A ⦄ ⦃ B'' : ToCvar B ⦄
                 → ⦃ A' : Operand {d}{k} A ⦄ ⦃ B' : Operand {d}{k} B ⦄
                 → A → B → Statement c-mach
          helper op₁ op₂ with access? A' | CType? (typeOf? A')
          ...            |    ReadWrite  | ✓                  = ⟪ [ toCvar op₁ +≔ toCvar op₂ ] ∣  ✓ ⟫
          ...            |    ReadOnly   | _                   = ⟪ [ toCvar op₁ +≔ toCvar op₂ ] ∣ error: ReadOnlyOperand ⟫
          ...            |    _          | err'                = ⟪ [ toCvar op₁ +≔ toCvar op₂ ] ∣ err' ⟫
