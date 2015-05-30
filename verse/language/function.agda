module verse.language.function where

open import Data.List           public
                                renaming ( _∷_ to _▸_ )
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
infix  6 ⟪_∣_⟫ _⟧ _◾
infix  7 rw ro


_◾ : {A : Set} → A → List A
lst ◾ = lst ▸ []


private
  Typeⁿ : ℕ → Set
  Typeⁿ zero        = ⊤
  Typeⁿ (suc zero)    = {d : Dim}{k : Kind {d} ✓} → Type k
  Typeⁿ (suc (suc n)) = ({d : Dim}{k : Kind {d} ✓} → Type k) × Typeⁿ (suc n)


-- Data type that captures a single argument declaration.
data VarDecl : Set where
  rw : {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl
  ro : {d : Dim}{k : Kind {d} ✓} → Type k → VarDecl


-- Data type that captures a series of argument declarations of a function.
data ArgDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _⟧   : VarDecl → ArgDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → VarDecl
       → ArgDecl {suc n} (Typeⁿ (suc n))
       → ArgDecl {suc (suc n)} (Typeⁿ (suc (suc n)))
  ⟦_   : {n : ℕ} → ArgDecl {suc n} (Typeⁿ (suc n))
       → ArgDecl {suc n} (Typeⁿ (suc n))


-- Data type that captures a series of local declarations in a function.
data LocalDecl : {n : ℕ} → Set → Set where
  void : LocalDecl {zero} (Typeⁿ zero)
  _⟧   : VarDecl → LocalDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → VarDecl
       → LocalDecl {suc n} (Typeⁿ (suc n))
       → LocalDecl {suc (suc n)} (Typeⁿ (suc (suc n)))
  ⟦_   : {n : ℕ} → LocalDecl {suc n} (Typeⁿ (suc n))
       → LocalDecl {suc n} (Typeⁿ (suc n))


-- Data type that captures a statment in a block.
data Statement {arch : Arch}(mach : Machine arch) : Set where
  ⟪_∣_⟫ : List (instruction arch) → Error (UserError arch) → Statement mach


-- Data type that captures a block of statements.
data Block {arch : Arch}(mach : Machine arch) : Set where
  void      : Block mach
  Begin_End : List (Statement mach) → Block mach


private
  funcType : {arch : Arch}(mach : Machine arch)
           → {n₁ n₂ : ℕ}
           → ArgDecl {n₁} (Typeⁿ n₁)
           → LocalDecl {n₂} (Typeⁿ n₂)
           → Set
  funcType {arch} mach void void = Block mach
  funcType {arch} mach void (rw ty ⟧)        = Local arch ReadWrite ty → funcType mach void void
  funcType {arch} mach void (ro ty ⟧)        = Local arch ReadOnly ty → funcType mach void void
  funcType {arch} mach void (rw ty ∣ rest)   = Local arch ReadWrite ty → funcType mach void rest
  funcType {arch} mach void (ro ty ∣ rest)   = Local arch ReadOnly ty → funcType mach void rest
  funcType {arch} mach void (⟦ all)          = funcType mach void all
  funcType {arch} mach (rw ty ⟧) rest        = Parameter arch ReadWrite ty → funcType mach void rest
  funcType {arch} mach (ro ty ⟧) rest        = Parameter arch ReadOnly ty → funcType mach void rest
  funcType {arch} mach (rw ty ∣ rest₁) rest₂ = Parameter arch ReadWrite ty → funcType mach rest₁ rest₂
  funcType {arch} mach (ro ty ∣ rest₁) rest₂ = Parameter arch ReadOnly ty → funcType mach rest₁ rest₂
  funcType {arch} mach (⟦ all) rest          = funcType mach all rest


-- Data type that captures a function declaration type.
data FuncDecl {arch : Arch}(mach : Machine arch) : Set where
  function : {n₁ n₂ : ℕ} → String
           → (args : ArgDecl {n₁} (Typeⁿ n₁))
           → (locals : LocalDecl {n₂} (Typeⁿ n₂))
           → (f : funcType mach args locals)
           → FuncDecl mach
