module

public import Silmaril.Formats.Compression.Checksum.Adler32Spec
public import Silmaril.Raw.Formats.Compression.Checksum.Adler32

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Checksum.Adler32Spec`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

/-! ### Small statement checks

The nonzero seed and wraparound examples exercise both seed components and
modular reduction; the last example records why canonical seeds are required.
-/

theorem adler32StateSpec_empty : adler32StateSpec 7 11 [] = (7, 11) := by decide

theorem adler32StateSpec_two_bytes :
    adler32StateSpec 7 11 [2, 3] = (12, 32) := by decide

theorem adler32StateSpec_wrap :
    adler32StateSpec 65520 65520 [1, 2] = (2, 1) := by decide

theorem adler32StateSpec_noncanonical_empty :
    adler32Fold (65521, 0) [] ≠ adler32StateSpec 65521 0 [] := by decide

theorem adler32Symbolic_empty : adler32Symbolic [] = 1 := by decide

/-! ### Refinement of the byte-by-byte definition -/

/-- The byte fold implements the symbolic state formula for canonical seeds.
The statement also permits natural-number inputs larger than bytes; applying
it to actual bytes requires no additional hypotheses. -/
theorem adler32Fold_eq_stateSpec (a b : Nat) (data : List Nat)
    (ha : a < adlerMod) (hb : b < adlerMod) :
    adler32Fold (a, b) data = adler32StateSpec a b data := by
  induction data generalizing a b with
  | nil =>
    simp [adler32Fold, adler32StateSpec, adlerWeightedSum,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  | cons x xs ih =>
    change adler32Fold ((a + x) % adlerMod, (b + (a + x) % adlerMod) % adlerMod) xs = _
    rw [ih _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
    simp only [adler32StateSpec, List.sum_cons, List.length_cons, adlerWeightedSum]
    apply Prod.ext
    · simp [Nat.add_assoc]
    · have hpoly : b + (xs.length + 1) * a +
          ((xs.length + 1) * x + adlerWeightedSum xs) =
          b + (a + x) + xs.length * (a + x) + adlerWeightedSum xs := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
        omega
      rw [hpoly]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The existing checksum definition equals the closed-form polynomial. -/
theorem adler32OfList_eq_symbolic (data : List Nat) :
    adler32OfList data = adler32Symbolic data := by
  unfold adler32OfList
  rw [adler32Fold_eq_stateSpec 1 0 data (by decide) (by decide)]
  simp [adler32StateSpec, adler32Symbolic]

/-- The byte-array API computes the symbolic checksum. -/
theorem adler32_eq_symbolic (data : ByteArray) :
    adler32 data = UInt32.ofNat (adler32Symbolic (data.data.toList.map UInt8.toNat)) := by
  simp [adler32, adler32OfList_eq_symbolic]

/-- Packing the symbolic accumulators fits in 32 bits without truncation. -/
theorem adler32Symbolic_lt (data : List Nat) : adler32Symbolic data < 2 ^ 32 := by
  rw [← adler32OfList_eq_symbolic]
  exact adler32OfList_lt data

theorem adler32_toNat_eq_symbolic (data : ByteArray) :
    (adler32 data).toNat = adler32Symbolic (data.data.toList.map UInt8.toNat) := by
  rw [adler32_eq_symbolic]
  exact Nat.mod_eq_of_lt (adler32Symbolic_lt _)

/-! ### Combining independently computed checksums -/

theorem adler32CombineState_zero_first :
    adler32CombineState (0, 0) (1, 1) 1 = (0, 0) := by decide

theorem adlerWeightedSum_append (xs ys : List Nat) :
    adlerWeightedSum (xs ++ ys) =
      adlerWeightedSum xs + ys.length * xs.sum + adlerWeightedSum ys := by
  induction xs with
  | nil => simp [adlerWeightedSum]
  | cons x xs ih =>
    simp only [List.cons_append, adlerWeightedSum, List.length_append, List.sum_cons, ih]
    simp only [Nat.add_mul, Nat.mul_add]
    omega

/-- A checksum of a concatenation is computed from the two checksums and the
length of the right input, without rereading either input. -/
theorem adler32StateSpec_append_combine (xs ys : List Nat) :
    adler32StateSpec 1 0 (xs ++ ys) =
      adler32CombineState (adler32StateSpec 1 0 xs) (adler32StateSpec 1 0 ys) ys.length := by
  simp only [adler32StateSpec, adler32CombineState, List.sum_append, List.length_append,
    adlerWeightedSum_append, Nat.zero_add, Nat.mul_one]
  apply Prod.ext
  · have hp : 1 + (xs.sum + ys.sum) + adlerMod =
        (1 + xs.sum) + (1 + ys.sum) + 65520 := by
      simp only [adlerMod]
      omega
    calc
      (1 + (xs.sum + ys.sum)) % adlerMod =
          (1 + (xs.sum + ys.sum) + adlerMod) % adlerMod := by simp
      _ = ((1 + xs.sum) + (1 + ys.sum) + 65520) % adlerMod := by rw [hp]
      _ = _ := by simp only [Nat.add_mod, Nat.mod_mod]
  · have hp : xs.length + ys.length +
          (adlerWeightedSum xs + ys.length * xs.sum + adlerWeightedSum ys) +
          ys.length * adlerMod =
          (xs.length + adlerWeightedSum xs) + (ys.length + adlerWeightedSum ys) +
            ys.length * ((1 + xs.sum) + 65520) := by
      simp only [adlerMod, Nat.mul_add, Nat.mul_one]
      omega
    calc
      (xs.length + ys.length +
          (adlerWeightedSum xs + ys.length * xs.sum + adlerWeightedSum ys)) % adlerMod =
          (xs.length + ys.length +
            (adlerWeightedSum xs + ys.length * xs.sum + adlerWeightedSum ys) +
            ys.length * adlerMod) % adlerMod := by simp
      _ = ((xs.length + adlerWeightedSum xs) + (ys.length + adlerWeightedSum ys) +
          ys.length * ((1 + xs.sum) + 65520)) % adlerMod := by rw [hp]
      _ = _ := by simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The independently computed states in the combine formula can be obtained
from the original byte fold. -/
theorem adler32Fold_append_combine (xs ys : List Nat) :
    adler32Fold (1, 0) (xs ++ ys) =
      adler32CombineState (adler32Fold (1, 0) xs) (adler32Fold (1, 0) ys) ys.length := by
  simp only [adler32Fold_eq_stateSpec 1 0 _ (by decide) (by decide)]
  exact adler32StateSpec_append_combine xs ys

end Silmaril.Formats.Compression
