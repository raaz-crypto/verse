module verse.arch.c where

open import verse.language.arch
open import verse.language.types
open import Data.String
open import verse.error
open import Data.Unit public using () renaming ( tt to scalar )
open import Data.Nat using  (ℕ ; suc)

data CInstruction (arch : Arch) : Set where
  _≔_+_ : {op₁ op₂ : OpType} → Operand arch ReadWrite → Operand arch op₁ → Operand arch op₂ → CInstruction arch
  _≔_-_ : {op₁ op₂ : OpType} → Operand arch ReadWrite → Operand arch op₁ → Operand arch op₂ → CInstruction arch
  _≔_*_ : {op₁ op₂ : OpType} → Operand arch ReadWrite → Operand arch op₁ → Operand arch op₂ → CInstruction arch
  _≔_/_ : {op₁ op₂ : OpType} → Operand arch ReadWrite → Operand arch op₁ → Operand arch op₂ → CInstruction arch
  _≔_%_ : {op₁ op₂ : OpType} → Operand arch ReadWrite → Operand arch op₁ → Operand arch op₂ → CInstruction arch
  _++   : Operand arch ReadWrite → CInstruction arch
  _−−   : Operand arch ReadWrite → CInstruction arch
  _≐_   : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch
  _+≐_  : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch
  _-≐_  : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch
  _*≐_  : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch
  _/≐_  : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch
  _%≐_  : {op : OpType} → Operand arch ReadWrite → Operand arch op → CInstruction arch

data CRegister : Set where
  〈_ofType_〉 : {d : Dim}{k : Kind {d} ✓} → String → Type k → CRegister

data CConstant : Set where

-- typeOfCRegister : {d : Dim}{k : Kind {d} ✓} → CRegister → Type k

-- -- c-arch : Arch
-- -- c-arch = MakeArch CInstruction CRegister CRegister CConstant 
