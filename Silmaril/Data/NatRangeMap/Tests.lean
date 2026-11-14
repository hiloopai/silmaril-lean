module

import Silmaril.Data.NatRangeMap.Thms

/-!
# Finite range maps: kernel-checked examples

Every example is checked by kernel reduction (`decide`, `rfl`); nothing is printed.
-/

namespace Silmaril.Data.NatRangeMap.Tests

open Silmaril.Data

/-- `[10, 19] ↦ 1`, then `[15, 24] ↦ 2`, `[30, 30] ↦ 1`, erase `[17, 18]`,
then `[25, 29] ↦ 1` joining `[30, 30]`. -/
def m₁ : NatRangeMap Nat :=
  ((((NatRangeMap.empty.assign 10 9 1).assign 15 9 2).assign 30 0 1).erase 17 1).assign 25 4 1

example : m₁.find? 9 = none := by decide
example : m₁.find? 10 = some 1 := by decide
example : m₁.find? 14 = some 1 := by decide
example : m₁.find? 15 = some 2 := by decide
example : m₁.find? 16 = some 2 := by decide
example : m₁.find? 17 = none := by decide
example : m₁.find? 18 = none := by decide
example : m₁.find? 19 = some 2 := by decide
example : m₁.find? 24 = some 2 := by decide
example : m₁.find? 27 = some 1 := by decide
example : m₁.find? 30 = some 1 := by decide
example : m₁.find? 31 = none := by decide
example : m₁.find? 1000000000000 = none := by decide

/-- Runs are maximal: `[25, 29]` and `[30, 30]` merged. -/
example : m₁.toList = [(10, 4, 1), (15, 1, 2), (19, 5, 2), (25, 5, 1)] := by decide
example : m₁.toList = [(10, 4, 1), (15, 1, 2), (19, 5, 2), (25, 5, 1)] := rfl

/-- The same map built differently. -/
def m₂ : NatRangeMap Nat :=
  ((((((NatRangeMap.empty.assign 25 0 1).assign 26 4 1).assign 19 5 2).assign 0 16 2).erase 0 9).assign
    10 4 1).erase 17 1

example : m₁ = m₂ := by decide
example : m₁ ≠ m₁.assign 17 0 2 := by decide
/-- Re-filling the erased hole with the neighbouring value merges the runs. -/
example : m₁.assign 17 1 2 = ((NatRangeMap.empty.assign 10 4 1).assign 15 9 2).assign 25 5 1 := by
  decide
example : (m₁.erase 0 100) = NatRangeMap.empty := by decide

/-- Large keys use `Nat` arithmetic, accelerated in the kernel. -/
example : ((NatRangeMap.empty : NatRangeMap Bool).assign (2 ^ 64) (2 ^ 32) true).find?
    (2 ^ 64 + 2 ^ 31) = some true := by decide

/-- `n` alternating runs `[3j, 3j + 1] ↦ j % 2`, built by appending (each `assign`
walks all earlier runs, so building costs O(n²) kernel steps). -/
def stripes (n : Nat) : NatRangeMap Nat :=
  Nat.rec (motive := fun _ => NatRangeMap Nat) NatRangeMap.empty
    (fun j m => m.assign (3 * j) 1 (j % 2)) n

/-- The same runs built from the top down (each `assign` is O(1)). -/
def stripesDown (n : Nat) : NatRangeMap Nat :=
  Nat.rec (motive := fun _ => NatRangeMap Nat) NatRangeMap.empty
    (fun i m => m.assign (3 * (n - 1 - i)) 1 ((n - 1 - i) % 2)) n

example : (stripes 40).find? 118 = some 1 := by decide +kernel
example : (stripes 40).find? 119 = none := by decide +kernel
example : stripes 40 = stripesDown 40 := by decide +kernel
/-- Filling the gaps merges all runs with value `0`. -/
example : ((stripes 40).erase 0 1000).assign 0 119 0 = NatRangeMap.empty.assign 0 119 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
example : (stripesDown 1000).find? 2998 = some 1 := by decide +kernel
set_option maxRecDepth 20000 in
example : (stripesDown 1000).find? 2999 = none := by decide +kernel
set_option maxRecDepth 20000 in
example : (stripesDown 1000).find? 3000 = none := by decide +kernel
set_option maxRecDepth 20000 in
example : (stripesDown 1000).toList.length = 1000 := by decide +kernel
set_option maxRecDepth 20000 in
example : NatRangeMap.ofList (stripesDown 1000).toList = stripesDown 1000 := by decide +kernel
set_option maxRecDepth 20000 in
example : (stripesDown 1000).assign 1 1 1 ≠ stripesDown 1000 := by decide +kernel

/-- `ofFn` represents a finitely supported function. -/
example : (NatRangeMap.ofFn (fun k => if k % 10 < 3 then some (k / 10) else none) 100).toList =
    (List.range 10).map fun i => (10 * i, 2, i) := by decide +kernel
example : NatRangeMap.ofFn (fun k => if k < 50 then some true else none) 100 =
    NatRangeMap.empty.assign 0 49 true := by decide +kernel

end Silmaril.Data.NatRangeMap.Tests
