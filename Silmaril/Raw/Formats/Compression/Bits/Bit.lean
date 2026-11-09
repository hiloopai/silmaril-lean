module

public import Silmaril.Formats.Compression.Bits.Bit

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Bits.Bit`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace Bit

@[simp]
theorem toNat_false : toNat false = 0 := rfl

@[simp]
theorem toNat_true : toNat true = 1 := rfl

/-! ### Round trips -/

/-- `nToBitsLSB` really is the base-2 decomposition of `n`. -/
theorem bitsToNatLSB_nToBitsLSB (n : Nat) : bitsToNatLSB (nToBitsLSB n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [nToBitsLSB]
    split
    · next h => simp [h, bitsToNatLSB]
    · next h =>
      rw [bitsToNatLSB, ih (n / 2) (by omega)]
      by_cases h2 : n % 2 = 1 <;> simp [h2] <;> omega

end Bit

end Silmaril.Formats.Compression
