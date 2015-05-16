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
  _+≔_  : CVariable → CVariable → CInstruction


data CConstant : Set where

{-
data CInstruction : Set where
  cComment : List (String) → CInstruction
  cinst    : RawCInstruction → String → CInstruction
-}

c-arch : Arch
c-arch = MakeArch CInstruction CVariable CVariable CConstant 

-- ToCVar typeclass, those Type which can be converted to a CVariable

record ToCvar {d : Dim}{k : Kind {d} ✓}(A : Access → Type k → Set) : Set where
  field
    toCvar : {acc : Access}{ty : Type k}(a : A acc ty) → CVariable


private
  module OperandToCvar {d : Dim}{k : Kind {d} ✓} where

    paramToCvar : {acc : Access}{ty : Type k} → ToCvar (Parameter c-arch)
    paramToCvar = record { toCvar = helper}
      where helper : {acc : Access}{ty : Type k}(a : Parameter c-arch acc ty) → CVariable
            helper (param _ x) = x

    regToCvar : {acc : Access}{ty : Type k} → ToCvar (Register c-arch)
    regToCvar = record { toCvar = helper}
      where helper : {acc : Access}{ty : Type k}(a : Register c-arch acc ty) → CVariable
            helper (reg _ x) = x

    localToCvar : {acc : Access}{ty : Type k} → ToCvar (Local c-arch)
    localToCvar = record { toCvar = helper}
      where helper : {acc : Access}{ty : Type k}(a : Local c-arch acc ty) → CVariable
            helper (localStack _ x) = x
            helper (localReg _ x) = x

open OperandToCvar

-- Define C Instructions


open Arch
open ToCvar ⦃...⦄


cAddEq : {d : Dim}{k : Kind {d} ✓}
       → ∀ {A B : Access → Type k → Set} ⦃ A' : ToCvar A ⦄ ⦃ B' : ToCvar B ⦄
       → AddEq {arch = c-arch} A B
cAddEq = record { _+≔_ = helper}
  where helper : {d : Dim}{k : Kind {d} ✓}{A B : Access → Type k → Set}
               → ⦃ A' : ToCvar A ⦄ ⦃ B' : ToCvar B ⦄
               → {acc : Access} {ty : Type k}
               → A ReadWrite ty → B acc ty → List (instruction c-arch)
        helper op₁ op₂ = [ (toCvar op₁) CInstruction.+≔ (toCvar op₂) ]



{-
toCVar : {acc : Access}{d : Dim}{k : Kind {d} ✓}{ty : Type k} → Operand c-arch acc ty → CVariable
toCVar (param ty x) = x
toCVar (reg ty x) = x
toCVar (local ty (onStack x)) = x
toCVar (local ty (inRegister x)) = x
-}

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
