-- This module is temporary and is used for experimentation 
-- and debugging during development.
module verse.try where

open import Data.Nat
open import Data.Product
open import Data.Unit                   using (⊤)
open import IO
import IO.Primitive as Prim

open import verse.arch.c.c-arch
open import verse.arch.c.c-instructions
open import verse.endian
open import verse.language.arch
open import verse.language.function
open import verse.language.instructions
open import verse.language.types
open import verse.language.userError
open import verse.util.typeEq

open Arch
open Operand


op1 : Parameter c-arch ReadWrite (word 2 host)
op1 = param (cvar "op1")

op2 : Register c-arch ReadOnly (word 2 host)
op2 = reg (cvar "op2")

open AddEq ⦃...⦄

try : Statement c-mach
try = op1 +← op2

----------------------------------------------------------
-- For compilation in MAlonzo backend
{-
hw : String
hw = "Hello World Abhijaju"

main' : IO ⊤
main' = putStr hw

main : Prim.IO ⊤
main = run main'
-}
----------------------------------------------------------

foo : FuncDecl c-mach
foo = function "foo" (⟦ rw Host16 ∣ ro Host32 ⟧) (⟦ rw Host16 ∣ ro (word 7 big) ∣ rw (array ⟨ 5 , 6 ⟩ of Host64) ⟧)
       (λ p1 p2 l1 l2 arr → 
         Begin
           p1 +← p1 ∷
           p1 +← p1 ∷
           p1 +← p1 ∷
           []
         End
       )

----------------------------------------------------------

ty1 : Type ⟨ 5 , 7 ⟩
ty1 = array ⟨ 5 , 7 ⟩ of Host16

ty2 : Type (⟨ 5 , 7 ⟩)
ty2 = array ⟨ 5 , 7 ⟩ of Host16


eq : Bool
eq = _type≟_ {c-arch} ty1 ty2
