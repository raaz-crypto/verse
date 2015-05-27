module verse.language.function where

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Unit           using ( ⊤ )

open import verse.language.arch
open import verse.language.machine
open import verse.language.types
open import verse.language.userError

open Arch

infix  4 ⟦_
infixr 5 _∣_
infix  6 ⟪_∣_⟫ _⟧
infix  7 rw ro


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
  rw : VarType → {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl
  ro : VarType → {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl


-- Data type that captures a series of argument declarations of a function.
data ArgDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _⟧  : VarDecl → ArgDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → VarDecl → ArgDecl {suc n} (Typeⁿ (suc n)) → ArgDecl {suc (suc n)} (Typeⁿ (suc (suc n)))
  ⟦_   : {n : ℕ} → ArgDecl {suc n} (Typeⁿ (suc n)) → ArgDecl {suc n} (Typeⁿ (suc n))

{-
-- Data type that captures a series of local declarations in a function.
data LocalDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _⟧  : VarDecl → ArgDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → VarDecl → ArgDecl {suc n} (Typeⁿ (suc n)) → ArgDecl {suc (suc n)} (Typeⁿ (suc (suc n)))
  ⟦_   : {n : ℕ} → ArgDecl {suc n} (Typeⁿ (suc n)) → ArgDecl {suc n} (Typeⁿ (suc n))
-}

-- Data type that captures a statment in a block.
data Statement {arch : Arch}(mach : Machine arch) : Set where
  ⟪_∣_⟫ : List (instruction arch) → (err : Error (UserError arch)) → Statement mach


-- Data type that captures a block of statements.
data Block {arch : Arch}(mach : Machine arch) : Set where
  void      : Block mach
  Begin_End : List (Statement mach) → Block mach


private
  funcType : {arch : Arch}(mach : Machine arch) → {n : ℕ} → ArgDecl {n} (Typeⁿ n) → Set
  funcType {arch} mach void = Block mach
  funcType {arch} mach (rw param ty ⟧)      = Parameter arch ReadWrite ty → funcType mach void
  funcType {arch} mach (rw local ty ⟧)      = Local arch ReadWrite ty → funcType mach void
  funcType {arch} mach (ro param ty ⟧)      = Parameter arch ReadOnly ty → funcType mach void
  funcType {arch} mach (ro local ty ⟧)      = Local arch ReadOnly ty → funcType mach void
  funcType {arch} mach (rw param ty ∣ rest) = Parameter arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (rw local ty ∣ rest) = Local arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (ro param ty ∣ rest) = Parameter arch ReadOnly ty → funcType mach rest
  funcType {arch} mach (ro local ty ∣ rest) = Local arch ReadOnly ty → funcType mach rest
  funcType {arch} mach (⟦ all)              = funcType mach all

{-
private
  funcType : {arch : Arch}(mach : Machine arch) → {n : ℕ} → ArgDecl {n} (Typeⁿ n) → Set
  funcType {arch} mach void                = Block mach
  funcType {arch} mach (rw param ty ∣ rest) = Parameter arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (ro param ty ∣ rest) = Parameter arch ReadOnly ty → funcType mach rest
  funcType {arch} mach (rw local ty ∣ rest) = Local arch ReadWrite ty → funcType mach rest
  funcType {arch} mach (ro local ty ∣ rest) = Local arch ReadOnly ty → funcType mach rest
-}

-- Data type that captures a function declaration type.
data FuncDecl {arch : Arch}(mach : Machine arch) : Set where
  function : {n : ℕ} → String → (args : ArgDecl {n} (Typeⁿ n)) → (f : funcType mach args) → FuncDecl mach
