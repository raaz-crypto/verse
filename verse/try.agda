module verse.try where

open import Data.List
open import Data.Nat
open import Data.String
open import Data.Unit using (⊤)
open import IO
import IO.Primitive as Prim


open import verse.arch.c.c-arch
open import verse.arch.c.c-instructions
open import verse.error
open import verse.language.arch
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

operands : ℕ → Set
operands 0 = List (instruction c-arch)
operands (suc x) = Parameter c-arch ReadWrite Host16 → operands x


func : operands 3
func  = λ op1 op2 op3 → op1 +≔ op2 Data.List.++ op2 +≔ op3 Data.List.++ op1 +≔ op3
