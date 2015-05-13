module verse.arch.c where

open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import Data.String
open import Data.List
open import Data.Nat
open import verse.error

-- Define C Architecture

{-
private
  module declarations {d : Dim}{k : Kind {d} ✓} where

    data CRegister : Type k → Set where
      〈_ofType_〉 : String → (ty : Type k) → CRegister ty

    typeOfCRegister : {ty : Type k} → CRegister ty → Type k
    typeOfCRegister 〈 _ ofType ty 〉 = ty

    specTypeOfC : {ty : Type k}(r : CRegister ty) → typeOfCRegister {ty} r ≡ ty
    specTypeOfC 〈 _ ofType ty 〉 = refl  

open declarations  
-}


data CVariable : Set where
  cvar_ : String → CVariable


data CInstruction : Set where
  _≔_+_ : CVariable → CVariable →  CVariable → CInstruction
  _+≔_  : CVariable → CVariable → CInstruction


data CConstant : Set where


c-arch : Arch
c-arch = MakeArch CInstruction CVariable CVariable CConstant


-- Define C Instructions

cAddEq : AddEq {arch = c-arch}(reg ty (cvar x₁))(reg ty (cvar x₂))
cAddEq = record { _+≔_ = x₁ CInstruction.+≔ x₂ :: []}

{-
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
-}

-- Define C Machine
{-
CRegister? : CRegister → Error (MachineError c-arch)
CRegister? _ = ✓


CInstruction? : CInstruction → Error (MachineError c-arch)
CInstruction? (_ CInstruction.+≔ _) = ✓
CInstruction? other = error: Instruction other Unsupported


c-mach : Machine c-arch
c-mach = MakeMachine CRegister? CInstruction?
-}
