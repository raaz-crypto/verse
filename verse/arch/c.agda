module verse.arch.c where

open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import Data.String
open import Data.List
open import verse.error

data CRegister : Set where
  〈_ofType_〉 : {d : Dim}{k : Kind {d} ✓} → String → Type k → CRegister

data CInstruction : Set where
  _≔_+_ : CRegister → CRegister → CRegister → CInstruction
  _≔_-_ : CRegister → CRegister → CRegister → CInstruction
  _≔_*_ : CRegister → CRegister → CRegister → CInstruction
  _≔_/_ : CRegister → CRegister → CRegister → CInstruction
  _≔_%_ : CRegister → CRegister → CRegister → CInstruction
  _++   : CRegister → CInstruction
  _−−   : CRegister → CInstruction
  _≔_   : CRegister → CRegister → CInstruction
  _+≔_  : CRegister → CRegister → CInstruction
  _-≔_  : CRegister → CRegister → CInstruction
  _*≔_  : CRegister → CRegister → CInstruction
  _/≔_  : CRegister → CRegister → CInstruction
  _%≔_  : CRegister → CRegister → CInstruction

data CConstant : Set where

-- typeOfCRegister : CRegister → {d : Dim}{k : Kind {d} ✓} → Type k
-- typeOfCRegister 〈 _ ofType ty 〉 {d} {k} = {!!}

c-arch : Arch
c-arch = MakeArch CInstruction CRegister CRegister CConstant 

open AddEq ⦃ ... ⦄
open Arch

cAddEq : AddEq c-arch
cAddEq = record { _+≔_ = caddeq }
  where caddeq : {op : OpType} → Operand c-arch ReadWrite → Operand c-arch op → List (instruction c-arch)
        caddeq (param var₁ _) (param var₂ _) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (param var₁ _) (reg var₂) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (param var₁ _) (local (onStack var₂ _)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (param var₁ _) (local (inRegister var₂)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (reg var₁) (param var₂ _) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (reg var₁) (reg var₂) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (reg var₁) (local (onStack var₂ _)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (reg var₁) (local (inRegister var₂)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (onStack var₁ _)) (param var₂ _) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (inRegister var₁)) (param var₂ _) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (onStack var₁ _)) (reg var₂) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (inRegister var₁)) (reg var₂) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (onStack var₁ _)) (local (onStack var₂ _)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (onStack var₁ _)) (local (inRegister var₂)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (inRegister var₁)) (local (onStack var₂ _)) = var₁ CInstruction.+≔ var₂ ∷ []
        caddeq (local (inRegister var₁)) (local (inRegister var₂)) = var₁ CInstruction.+≔ var₂ ∷ []
