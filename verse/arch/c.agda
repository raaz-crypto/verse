module verse.arch.c where

open import verse.language.arch
open import verse.language.types
open import Data.String
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
-- typeOfCRegister 〈 _ ofType ty 〉 = ty

c-arch : Arch
c-arch = MakeArch CInstruction CRegister CRegister CConstant 
