module verse.try where

open import Data.List
open import Data.Nat
open import Data.Product
open import Data.String                 hiding (_++_)
open import Data.Unit                   using (⊤)
open import IO
import IO.Primitive as Prim

open import verse.arch.c.c-arch
open import verse.arch.c.c-instructions
open import verse.endian
open import verse.error
open import verse.language.arch
open import verse.language.function
open import verse.language.instructions
open import verse.language.types

open Arch
open Operand

op1 : Parameter c-arch ReadWrite Host16
op1 = param (cvar "op1")

op2 : Register c-arch ReadOnly Host16
op2 = reg (cvar "op2")

open AddEq ⦃...⦄

try : List (instruction c-arch)
try = op1 +≔ op2

----------------------------------------------------------
{-
hw : String
hw = "Hello World Abhijaju"

main' : IO ⊤
main' = putStr hw

main : Prim.IO ⊤
main = run main'
-}
----------------------------------------------------------

more : ℕ → Set
more 0 = ℕ
more (suc x) = ℕ → more x

my_sum : ∀ {x : ℕ} → ℕ → more x
my_sum {0}   a = a
my_sum {suc x} a = λ m → my_sum {x} (m + a)

----------------------------------------------------------


foo0 : FuncDecl c-arch
foo0 = function "foo" void []

foo1 : FuncDecl c-arch
foo1 = function "foo" (● param Host16 , void) (λ op3 → op3 +≔ op3 ++ op3 +≔ op3 ++ op3 +≔ op3 ++ op3 +≔ op3 ++ op3 +≔ op3 ++ op3 +≔ op3)

{-
foo2 : Function c-arch {3} ⟪ {!!} ⟫
foo2 = function "foo" {!!} λ op1 → []
-}
