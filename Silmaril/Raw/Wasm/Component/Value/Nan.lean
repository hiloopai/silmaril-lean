module

public import Silmaril.Wasm.Component.Reference.Value.Nan.Defs

public import Silmaril.Raw.Wasm.Component.ABI.FloatChar.Properties
public import Silmaril.Raw.Wasm.Component.Features

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

/-- A lowering is invisible to a subsequent lift (`canonicalize_nan*`). -/
theorem NanLower.canonicalizeNaN_eq {prof : ProfileKind} {t : FloatType}
    {x y : BitVec t.width} (h : NanLower prof t x y) :
    ABI.canonicalizeNaN t y = ABI.canonicalizeNaN t x :=
  (nanLower_nondet_iff.mp h.to_nondet).canonicalizeNaN_eq

/-- Passthrough (wasmtime) is admitted by `nondet`. -/
theorem nanLower_self_nondet (t : FloatType) (x : BitVec t.width) :
    NanLower .nondet t x x := by
  simp only [NanLower]
  split <;> simp_all

/-! ## Tests: passthrough of the negative quiet NaN `0xffc00000` -/

theorem nanLower_nondet_passthrough :
    NanLower .nondet .f32 negQuietNaN32 negQuietNaN32 := by decide

theorem not_nanLower_deterministic_passthrough :
    ¬ NanLower .deterministic .f32 negQuietNaN32 negQuietNaN32 := by decide

theorem not_nanLower_refStrict_passthrough :
    ¬ NanLower .refStrict .f32 negQuietNaN32 negQuietNaN32 := by decide

theorem nanLower_refStrict_random :
    NanLower .refStrict .f32 negQuietNaN32 randomNaN32 := by decide

theorem nanLower_deterministic_canonical :
    NanLower .deterministic .f32 negQuietNaN32 (ABI.canonicalNaN .f32) := by decide

end Silmaril.Wasm.Component.Value
