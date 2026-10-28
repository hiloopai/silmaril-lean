module

public import Silmaril.Numeric.Float.Wasm

/-!
# Comparison facts for lowering proofs (architecture-independent)

Facts about `UnpackedFloat.compare` on decoded encodings, the relation
`Admits` away from NaN, and the zero encodings of binary32 and binary64, used to
verify instruction sequences that implement WebAssembly comparisons and
`fmin`/`fmax`. Nothing here depends on an instruction set; the x86-specific
minimum/maximum facts are in `Silmaril.X86.Float.Wasm.MinMax`.
-/

@[expose] public section

namespace Silmaril.Numeric.Float.Lowering

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Float

/-! ## `UnpackedFloat.compare`

`compare_swap`, `compare_eq_cases` and `compare_isSome` on `UnpackedFloat` are
stated in `Silmaril.Numeric.Float.Wasm`. -/

/-- Two encodings are unordered exactly when one of them is a NaN. -/
theorem compare_eq_none_iff {fmt : Format} (a b : Bits fmt) :
    a.value.compare b.value = none ↔ (a.isNaN || b.isNaN) = true := by
  constructor
  · intro h
    by_contra hn
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
    have := compare_isSome (Bits.value_ne_notANumber hn.1) (Bits.value_ne_notANumber hn.2)
    rw [h] at this
    cases this
  · intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [(Bits.value_eq_notANumber_iff a).mpr h]; rfl
    · rw [(Bits.value_eq_notANumber_iff b).mpr h]
      cases a.value <;> rfl

/-- Away from NaN references, `Admits` is equality. -/
theorem admits_iff_eq_of_not_nan {fmt : Format} {c : Bool} {reference result : Bits fmt}
    (h : reference.isNaN = false) : Admits c reference result ↔ result = reference := by
  unfold Admits
  simp [h]

/-- The zeros of binary32 and binary64. -/
theorem packedZero32 (s : Sign) :
    (packedZero .binary32 s : BitVec 32) = if s = .negative then 0x80000000#32 else 0#32 := by
  cases s <;> decide

theorem packedZero64 (s : Sign) :
    (packedZero .binary64 s : BitVec 64) =
      if s = .negative then 0x8000000000000000#64 else 0#64 := by
  cases s <;> decide


end Silmaril.Numeric.Float.Lowering
