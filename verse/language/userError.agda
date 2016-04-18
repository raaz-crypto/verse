module verse.language.userError where

open import verse.error          public
open import verse.language.arch
open import verse.language.types

open Arch ⦃...⦄


-- When generating instructions for a particular machine of a given
-- architecture there can be errors due to unsupported registers, instructions or type mismatch.
-- This type captures all such errors.
data UserError (arch : Arch) : Set where
  Register_Unsupported    : register    → UserError arch
  Instruction_Unsupported : instruction → UserError arch
  ReadOnlyOperand         : UserError arch
  Type_Unsupported        : {d : Dim} → Type d → UserError arch
  Type_MismatchWith_      : {d₁ d₂ : Dim} → Type d₁ → Type d₂ → UserError arch
