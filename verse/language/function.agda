module verse.language.function where

open import Data.List
open import Data.Nat
open import Data.Product        public
open import Data.String
open import Data.Unit           using (⊤)

open import verse.error
open import verse.language.arch
open import verse.language.types

open Arch

infix  5 ● ○ ⟪_⟫


private
  Typeⁿ : ℕ → Set
  Typeⁿ zero        = ⊤
  Typeⁿ (suc zero)    = {d : Dim}{k : Kind {d} ✓} → Type k
  Typeⁿ (suc (suc n)) = ({d : Dim}{k : Kind {d} ✓} → Type k) × Typeⁿ (suc n)


-- Data type that captures type of an argument, whether it is local or parameter.
data VarType : Set where
  param : VarType
  local : VarType


-- Data type that captures a single argument declaration.
data VarDecl : Set where
  ● : VarType → {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl
  ○ : VarType → {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl


-- Data type that captures a series of argument declaration of a function.
data ArgDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _∣_  : {n : ℕ} → VarDecl → ArgDecl {n} (Typeⁿ n) → ArgDecl {suc n} (Typeⁿ (suc n))


-- Data type that captures a statment in a block.
data Statement {arch : Arch}(mach : Machine arch) : Set where
  ⟪_⟫ : List (instruction arch) × Error (UserError arch) → Statement mach


-- Data type that captures a block of statements.
data Block {arch : Arch}(mach : Machine arch) : Set where
  void      : Block mach
  Begin_End : List (Statement mach) → Block mach


private
  funcType : {arch : Arch}(mach : Machine arch) → {n : ℕ} → ArgDecl {n} (Typeⁿ n) → Set
  funcType {arch} mach void                = Block mach
  funcType {arch} mach (● param ty ∣ rest) = Parameter arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (○ param ty ∣ rest) = Parameter arch ReadOnly ty → funcType mach rest
  funcType {arch} mach (● local ty ∣ rest) = Local arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (○ local ty ∣ rest) = Local arch ReadOnly ty → funcType mach rest


-- Data type that captures a function declaration type.
data FuncDecl {arch : Arch}(mach : Machine arch) : Set where
  function : {n : ℕ} → String → (args : ArgDecl {n} (Typeⁿ n)) → (f : funcType mach args) → FuncDecl mach
