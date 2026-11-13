module

public import Silmaril.Wasm.Examples.Farkas.Defs
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The Farkas checker: bounded `i64` arithmetic

Under the checker's bounds (`|input| ≤ 2³⁰`, `|accumulator| ≤ 2⁶²`) the `i64` operations of
the module are exact: `macc_toInt` (`acc + y * a` without wraparound), `toInt_i64c` (the
constants), and the comparisons used as range checks read as integer comparisons
(`ltS_ofInt`, `gtS_ofInt`). `bool32_eq_zero`, `or_eq_zero`: the sticky flag is `0` iff every
check passed.
-/

namespace Silmaril.Wasm.Examples.Farkas

open Silmaril.Wasm Silmaril.Wasm.Numerics

/-- A constant in the `i64` range reads back. -/
theorem toInt_ofInt64 {v : Int} (h₁ : -2 ^ 63 ≤ v) (h₂ : v < 2 ^ 63) : (BitVec.ofInt 64 v).toInt = v := by
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- **Exact multiply-accumulate** under the checker's bounds. -/
theorem macc_toInt {v y a : BitVec 64} (hv : -aB ≤ v.toInt ∧ v.toInt ≤ aB)
    (hy : -cB ≤ y.toInt ∧ y.toInt ≤ cB) (ha : -cB ≤ a.toInt ∧ a.toInt ≤ cB) :
    (v + y * a).toInt = v.toInt + y.toInt * a.toInt := by
  have hp : -(2 ^ 60) ≤ y.toInt * a.toInt ∧ y.toInt * a.toInt ≤ 2 ^ 60 := by
    simp only [cB] at hy ha
    constructor <;> nlinarith
  have hmul : (y * a).toInt = y.toInt * a.toInt := by
    rw [BitVec.toInt_mul]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [BitVec.toInt_add, hmul]
  simp only [aB] at hv
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem bool32_eq_zero {b : Bool} : bool32 b = 0 ↔ b = false := by
  cases b <;> simp [bool32]

theorem or_eq_zero {x y : BitVec 32} : (x ||| y) = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem ltS_ofInt {x : BitVec 64} {v : Int} (h₁ : -2 ^ 63 ≤ v) (h₂ : v < 2 ^ 63) :
    intRelOp .i64 (.lt .signed) x (BitVec.ofInt 64 v) = bool32 (decide (x.toInt < v)) := by
  show bool32 (decide (BitVec.toInt (n := 64) x < BitVec.toInt (BitVec.ofInt 64 v))) = _
  rw [toInt_ofInt64 h₁ h₂]

theorem gtS_ofInt {x : BitVec 64} {v : Int} (h₁ : -2 ^ 63 ≤ v) (h₂ : v < 2 ^ 63) :
    intRelOp .i64 (.gt .signed) x (BitVec.ofInt 64 v) = bool32 (decide (x.toInt > v)) := by
  show bool32 (decide (BitVec.toInt (n := 64) x > BitVec.toInt (BitVec.ofInt 64 v))) = _
  rw [toInt_ofInt64 h₁ h₂]

/-- The range check of `orOut` passes iff the value is in range. -/
theorem out_eq_zero {x : BitVec 64} {lo hi : Int} (h₁ : -2 ^ 63 ≤ lo) (h₂ : lo < 2 ^ 63)
    (h₃ : -2 ^ 63 ≤ hi) (h₄ : hi < 2 ^ 63) :
    (intRelOp .i64 (.lt .signed) x (BitVec.ofInt 64 lo) |||
      intRelOp .i64 (.gt .signed) x (BitVec.ofInt 64 hi)) = 0 ↔ lo ≤ x.toInt ∧ x.toInt ≤ hi := by
  rw [ltS_ofInt h₁ h₂, gtS_ofInt h₃ h₄, or_eq_zero, bool32_eq_zero, bool32_eq_zero]
  simp only [decide_eq_false_iff_not, not_lt, gt_iff_lt]

end Silmaril.Wasm.Examples.Farkas
