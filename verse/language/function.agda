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
  Typeⁿ (suc zero)    = {d : Dim} → Type d
  Typeⁿ (suc (suc n)) = ({d : Dim} → Type d) × Typeⁿ (suc n)


-- Data type that captures a single argument declaration.
data ArgVarDecl : Set where
  rw : {d : Dim} → Type d → ArgVarDecl
  ro : {d : Dim} → Type d → ArgVarDecl


-- Data type that captures a series of argument declarations of a function.
data ArgDecl : {n : ℕ} → Set → Set where
  void : ArgDecl {zero} (Typeⁿ zero)
  _⟧   : ArgVarDecl → ArgDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → ArgVarDecl
       → ArgDecl {suc n} (Typeⁿ (suc n))
       → ArgDecl {suc (suc n)} (Typeⁿ (suc (suc n)))
  ⟦_   : {n : ℕ} → ArgDecl {suc n} (Typeⁿ (suc n))
       → ArgDecl {suc n} (Typeⁿ (suc n))


-- Information to be used by allocator
data LocalType : Set where
  inReg    : LocalType
  onStack  : LocalType
  inAnyReg : LocalType
  auto     : LocalType


-- Data type that captures local variable declaration
data LocalVarDecl : Set where
  rw : LocalType → {d : Dim} → Type d → LocalVarDecl
  ro : LocalType → {d : Dim} → Type d → LocalVarDecl


-- Data type that captures a series of local declarations in a function.
data LocalDecl : {n : ℕ} → Set → Set where
  void : LocalDecl {zero} (Typeⁿ zero)
  _⟧   : LocalVarDecl → LocalDecl {suc zero} (Typeⁿ (suc zero))
  _∣_  : {n : ℕ} → LocalVarDecl
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
  funcLocal : {arch : Arch}(mach : Machine arch){n : ℕ}
            → LocalDecl {n} (Typeⁿ n)
            → Set
  funcLocal mach void                   = Block mach
  funcLocal {arch} mach (rw x ty ⟧)     = Local arch ReadWrite ty → funcLocal mach void
  funcLocal {arch} mach (ro x ty ⟧)     = Local arch ReadOnly ty → funcLocal mach void
  funcLocal {arch} mach (rw x ty ∣ rest) = Local arch ReadWrite ty → funcLocal mach rest
  funcLocal {arch} mach (ro x ty ∣ rest) = Local arch ReadOnly ty → funcLocal mach rest
  funcLocal {arch} mach (⟦ all)         = funcLocal mach all


-- To capture body of a function
record Body {arch : Arch}(mach : Machine arch) : Set where
  constructor body
  field
    {n}   : ℕ
    local : LocalDecl {n} (Typeⁿ n)
    func  : funcLocal {arch} mach local


private
  funcArg : {arch : Arch}(mach : Machine arch){n : ℕ}
          → ArgDecl {n} (Typeⁿ n)
          → Set
  funcArg {arch} mach void          = Body mach
  funcArg {arch} mach (rw ty ⟧)     = Parameter arch ReadWrite ty → funcArg mach void
  funcArg {arch} mach (ro ty ⟧)     = Parameter arch ReadOnly ty → funcArg mach void
  funcArg {arch} mach (rw ty ∣ rest) = Parameter arch ReadWrite ty → funcArg mach rest
  funcArg {arch} mach (ro ty ∣ rest) = Parameter arch ReadOnly ty → funcArg mach rest
  funcArg mach (⟦ all)              = funcArg mach all


-- Data type that captures a function declaration type.
data FuncDecl {arch : Arch}(mach : Machine arch) : Set where
  function : {n : ℕ} → String
           → (args : ArgDecl {n} (Typeⁿ n))
           → (f : funcArg mach args)
           → FuncDecl mach
