module verse.language.instructions where

open import verse.language.arch
open import verse.language.function
open import verse.language.machine
open import verse.language.types
open import verse.language.userError
open import verse.util.typeEq

open Arch
open Machine
open Operand


private
  module ArithmeticAssign {arch : Arch}{mach : Machine arch}{d : Dim}{k : Kind {d} ✓} where

    record AddEq (A B : Set) : Set where
      field
        ⦃ A' ⦄ : Operand {d}{k} A
        ⦃ B' ⦄ : Operand {d}{k} B
        _+≔_    : A → B → Statement mach

      _+←_ : ⦃ addEq : AddEq A B ⦄ → A → B → Statement mach
      _+←_ op₁ op₂ with access? A' | _type≟_ {arch} (typeOf? A') (typeOf? B') | type? mach (typeOf? A') 
      ...          |    ReadWrite  | true  | ✓     = op₁ +≔ op₂
      ...          |    ReadOnly   | _     | _      = ⟪ [] ∣ error: ReadOnlyOperand ⟫
      ...          |    _          | false | _      = ⟪ [] ∣ error: (Type (typeOf? A') MismatchWith (typeOf? B')) ⟫
      ...          |    _          | _     | err    = ⟪ [] ∣ err ⟫

open ArithmeticAssign public
