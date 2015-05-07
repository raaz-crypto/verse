module verse.arch.c where

open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import Data.String
open import Data.List
open import Data.Nat
open import verse.error

-- Define C Architecture

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


typeOfCRegister : {d : Dim}{k : Kind {d} ✓} → CRegister → Type k
typeOfCRegister {∞} {⟨∞⟩} 〈 x ofType word n x₁ 〉 = word n x₁ ⋆
typeOfCRegister {∞} {⟨∞⟩} 〈 x ofType array k of ty 〉 = (array k of ty) ⋆
typeOfCRegister {∞} {⟨∞⟩} 〈 x ofType word n x₁ ⋆ 〉 = word n x₁ ⋆
typeOfCRegister {∞} {⟨∞⟩} 〈 x ofType (array k of ty) ⋆ 〉 = (array k of ty) ⋆
typeOfCRegister {finite zero} {⟨ bs ⟩} 〈 x ofType word n x₁ 〉 = word n x₁
typeOfCRegister {finite (suc x₂)} {k} 〈 x ofType word n x₁ 〉 = array k of word n x₁
typeOfCRegister {finite zero} {⟨ bs ⟩} 〈 x ofType array k of word n₁ x₁ 〉 = word n₁ x₁
typeOfCRegister {finite (suc x₂)} {k₁} 〈 x ofType array k of word n₁ x₁ 〉 = array k₁ of word n₁ x₁
typeOfCRegister {finite zero} {⟨ bs ⟩} 〈 x ofType word n x₁ ⋆ 〉 = word n x₁
typeOfCRegister {finite (suc x₂)} {k} 〈 x ofType word n x₁ ⋆ 〉 = array k of (word n x₁)
typeOfCRegister {finite zero} {⟨ bs ⟩} 〈 x ofType (array k of word n₁ x₁) ⋆ 〉 = word n₁ x₁
typeOfCRegister {finite (suc x₂)} {k₁} 〈 x ofType (array k of word n₁ x₁) ⋆ 〉 = array k₁ of word n₁ x₁


c-arch : Arch
c-arch = MakeArch CInstruction CRegister CRegister CConstant typeOfCRegister


-- Define C Instructions

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


-- Define C Machine

CRegister? : CRegister → Error (MachineError c-arch)
CRegister? _ = ✓


CInstruction? : CInstruction → Error (MachineError c-arch)
CInstruction? (_ CInstruction.+≔ _) = ✓
CInstruction? other = error: Instruction other Unsupported


c-mach : Machine c-arch
c-mach = MakeMachine CRegister? CInstruction?
