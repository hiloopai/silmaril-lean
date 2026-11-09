module

public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Raw.Formats.Compression.Bits.Bit

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Checksum.Adler32`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

set_option maxRecDepth 20000

/-! ### Published check values

`String.toUTF8` does not reduce inside a `module`, so the vectors are spelled as
the ASCII bytes of the string, with the string given in the docstring. -/

/-- Adler-32 of empty input is 1. -/
theorem adler32_empty : adler32 ByteArray.empty = 1 := by decide

/-- RFC 1950 §9 worked example: the Adler-32 of the ASCII bytes of `"Wikipedia"`
is `0x11E60398`. -/
theorem adler32_check :
    adler32 (ByteArray.mk #[0x57, 0x69, 0x6B, 0x69, 0x70, 0x65, 0x64, 0x69, 0x61])
      = 0x11E60398 := by
  decide

/-- Published check value: the Adler-32 of `"123456789"` is `0x091E01DE`. -/
theorem adler32_check_123456789 :
    adler32 (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = 0x091E01DE := by
  decide

/-- Published check value: the Adler-32 of `"a"` is `0x00620062`. -/
theorem adler32_check_a : adler32 (ByteArray.mk #[0x61]) = 0x00620062 := by decide

/-! ### Incremental update -/

/-- Incremental-update law: the Adler-32 state of a concatenation is obtained by
running the second part from the state reached after the first. -/
theorem adler32Fold_append (st : Nat × Nat) (a b : List Nat) :
    adler32Fold st (a ++ b) = adler32Fold (adler32Fold st a) b := by
  simp [adler32Fold, List.foldl_append]

/-- `adler32OfList` reads off the final state, so the law above transfers. -/
theorem adler32OfList_append (a b : List Nat) :
    adler32OfList (a ++ b) =
      (adler32Fold (adler32Fold (1, 0) a) b).2 * 65536 + (adler32Fold (adler32Fold (1, 0) a) b).1 := by
  simp [adler32OfList, adler32Fold_append]

/-! ### Range -/

/-- Both accumulators stay below the modulus, so `adler32OfList` fits in 32 bits
and the `UInt32.ofNat` in `adler32` does not truncate. -/
theorem adler32Fold_lt (st : Nat × Nat) (data : List Nat)
    (h1 : st.1 < adlerMod) (h2 : st.2 < adlerMod) :
    (adler32Fold st data).1 < adlerMod ∧ (adler32Fold st data).2 < adlerMod := by
  induction data generalizing st with
  | nil => exact ⟨h1, h2⟩
  | cons x xs ih =>
    refine ih _ ?_ ?_ <;> simp [adler32UpdateByte, adlerMod] <;> omega

theorem adler32OfList_lt (data : List Nat) : adler32OfList data < 2 ^ 32 := by
  obtain ⟨h1, h2⟩ := adler32Fold_lt (1, 0) data (by decide) (by decide)
  simp only [adler32OfList, adlerMod] at *
  omega

end Silmaril.Formats.Compression
