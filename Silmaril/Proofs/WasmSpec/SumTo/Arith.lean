module

public import Silmaril.WasmSpec.SumTo.Defs

/-!
# `SumTo` v1: arithmetic of the triangular numbers

`tri_succ` (`tri (k + 1) = tri k + (k + 1)`), its `i32` image `triBV_step`
(`triBV i = triBV (i - 1) + i` for `i ≠ 0`), `triBV_zero`, and `sub_one_lt`
(the measure decreases). Shared by every solution of `Spec`.
-/

@[expose] public section

namespace Silmaril.WasmSpec.SumTo

/-- One more term of the sum. -/
theorem tri_succ (k : Nat) : tri (k + 1) = tri k + (k + 1) := by
  unfold tri
  have h : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by
    rw [Nat.mul_comm (k + 1) (k + 1 + 1), Nat.add_mul (k + 1) 1, Nat.add_mul k 1 (k + 1)]
    omega
  rw [h, Nat.add_mul_div_left _ _ (by decide)]

/-- `triBV 0 = 0`. -/
theorem triBV_zero : triBV 0 = 0 := rfl

/-- Decrementing a nonzero `i32` lowers its unsigned value by one. -/
theorem toNat_sub_one {i : BitVec 32} (hi : i ≠ 0) : (i - 1#32).toNat = i.toNat - 1 := by
  have h0 : i.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using hi
  rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
  simp

/-- The loop measure decreases. -/
theorem sub_one_lt {i : BitVec 32} (hi : i ≠ 0) : (i - 1#32).toNat < i.toNat := by
  have h0 : i.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using hi
  rw [toNat_sub_one hi]
  omega

/-- The `i32` triangular numbers step down by `i`. -/
theorem triBV_step {i : BitVec 32} (hi : i ≠ 0) : triBV i = triBV (i - 1#32) + i := by
  have h0 : i.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using hi
  obtain ⟨k, hk⟩ : ∃ k, i.toNat = k + 1 := ⟨i.toNat - 1, by omega⟩
  have h2 : tri i.toNat = tri (i.toNat - 1) + i.toNat := by
    rw [hk, tri_succ, Nat.add_sub_cancel]
  unfold triBV
  rw [toNat_sub_one hi, h2, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end Silmaril.WasmSpec.SumTo
