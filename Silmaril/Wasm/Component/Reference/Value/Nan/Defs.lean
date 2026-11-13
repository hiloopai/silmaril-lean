module

public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Properties.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.Wasm.Execution.Memory.Lemmas.Defs

/-!
# The NaN lowering policy of each profile

`NanLower prof t x y` says that lowering the float bits `x` may produce the bits `y`
under the profile `prof`. It is the C7 choice point (NaN bits on lower) of REF
`maybe_scramble_nan32` (L1491) / `maybe_scramble_nan64` and `random_nan_bits` (L1509) of
`definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
via `encode_float_as_i32/i64` and `lower_flat`, restricted per
`ProfileKind`:

* `nondet`: a NaN lowers to *some* NaN and a non-NaN is preserved. This is what the
  `CanonicalABI.md` §"Storing" prose admits, and it admits wasmtime `a7b4f29`'s bit-exact
  passthrough (`translate_f32`/`translate_f64` in `crates/environ/src/fact/trampoline.rs`), e.g. of
  `0xffc00000`.
* `refStrict`: a NaN lowers to a value in the image of REF `random_nan_bits`
  (`ABI.RandomNaNBits`: all-ones exponent, some fraction bit below the quiet bit).
  `ABI.ScrambleNaN false t x y` alone would be equivalent to `nondet` and admit passthrough of
  `0xffc00000`, so the restriction to `RandomNaNBits` is added.
* `deterministic`: REF `DETERMINISTIC_PROFILE`, `ABI.ScrambleNaN true` (the canonical
  NaN).

`isNaN`, canonicalization and `ScrambleNaN` are the definitions of `ABI.FloatChar`; nothing is
redefined here. No claim beyond the theorems below. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Value

open Silmaril.Wasm

/-- The admissible NaN lowerings per profile (REF `maybe_scramble_nan*`, choice
point C7). -/
def NanLower : ProfileKind → (t : FloatType) → BitVec t.width → BitVec t.width → Prop
  | .nondet, t, x, y => if ABI.isNaN t x then ABI.isNaN t y = true else y = x
  | .refStrict, t, x, y =>
      ABI.ScrambleNaN false t x y ∧ (ABI.isNaN t x = true → ABI.RandomNaNBits t y)
  | .deterministic, t, x, y => ABI.ScrambleNaN true t x y

/-- A decidable restatement of `ABI.RandomNaNBits`. -/
theorem randomNaNBits_iff (t : FloatType) (y : BitVec t.width) :
    ABI.RandomNaNBits t y ↔
      y.extractLsb' (ABI.floatFractionWidth t) (ABI.floatExponentWidth t) =
          BitVec.allOnes (ABI.floatExponentWidth t) ∧
        ∃ i, i < ABI.floatFractionWidth t - 1 ∧ y.getLsbD i = true := by
  unfold ABI.RandomNaNBits
  constructor
  · rintro ⟨h, i, hi, b⟩
    exact ⟨h, i, by omega, b⟩
  · rintro ⟨h, i, hi, b⟩
    exact ⟨h, i, by omega, b⟩

instance (t : FloatType) (y : BitVec t.width) : Decidable (ABI.RandomNaNBits t y) :=
  decidable_of_iff _ (randomNaNBits_iff t y).symm

instance (t : FloatType) (x y : BitVec t.width) : Decidable (ABI.ScrambleNaN true t x y) :=
  decidable_of_iff _ (ABI.scrambleNaN_true_iff t x y).symm

instance (t : FloatType) (x y : BitVec t.width) : Decidable (ABI.ScrambleNaN false t x y) :=
  decidable_of_iff _ (ABI.scrambleNaN_false_iff t x y).symm

instance (prof : ProfileKind) (t : FloatType) (x y : BitVec t.width) :
    Decidable (NanLower prof t x y) := by
  cases prof <;> unfold NanLower <;> infer_instance

/-! ## Tests: passthrough of the negative quiet NaN `0xffc00000` -/

/-- `0xffc00000`: the negative quiet NaN, neither canonical nor in the image of REF
`random_nan_bits`; wasmtime passes it through unchanged. -/
def negQuietNaN32 : BitVec FloatType.f32.width := 0xffc00000#32

/-- `0x7f800001`: a NaN in the image of REF `random_nan_bits`. -/
def randomNaN32 : BitVec FloatType.f32.width := 0x7f800001#32

end Silmaril.Wasm.Component.Value

namespace Silmaril.Wasm.Component.Value

open Silmaril.Wasm

/-- `nondet` is exactly `ScrambleNaN false`. -/
theorem nanLower_nondet_iff {t : FloatType} {x y : BitVec t.width} :
    NanLower .nondet t x y ↔ ABI.ScrambleNaN false t x y := by
  rw [ABI.scrambleNaN_false_iff]
  simp only [NanLower]
  cases hx : ABI.isNaN t x <;> simp

/-- Every `refStrict` lowering is admitted by `nondet`. -/
theorem NanLower.of_refStrict {t : FloatType} {x y : BitVec t.width}
    (h : NanLower .refStrict t x y) : NanLower .nondet t x y :=
  nanLower_nondet_iff.mpr h.1

/-- Every `deterministic` lowering is admitted by `nondet`. -/
theorem NanLower.of_deterministic {t : FloatType} {x y : BitVec t.width}
    (h : NanLower .deterministic t x y) : NanLower .nondet t x y := by
  simp only [NanLower] at h
  rw [ABI.scrambleNaN_true_iff] at h
  subst h
  exact nanLower_nondet_iff.mpr (ABI.scrambleNaN_canonicalizeNaN false t x)

/-- Every admissible lowering is admitted by `nondet`. -/
theorem NanLower.to_nondet {prof : ProfileKind} {t : FloatType} {x y : BitVec t.width}
    (h : NanLower prof t x y) : NanLower .nondet t x y := by
  cases prof
  · exact h
  · exact h.of_refStrict
  · exact h.of_deterministic

/-- The deterministic profile always admits the canonicalized value. -/
theorem nanLower_deterministic_canonicalizeNaN (t : FloatType) (x : BitVec t.width) :
    NanLower .deterministic t x (ABI.canonicalizeNaN t x) :=
  ABI.scrambleNaN_canonicalizeNaN true t x

end Silmaril.Wasm.Component.Value
