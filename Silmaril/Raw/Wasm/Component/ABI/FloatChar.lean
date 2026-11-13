module

public import Silmaril.Wasm.Component.Reference.ABI.FloatChar.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Memory

/-!
# Canonical floats and chars

Canonical ABI adapters for the WIT primitives `f32`, `f64`, and `char`, following
`definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b/design/mvp/canonical-abi/definitions.py>)
and `CanonicalABI.md` §"Loading", §"Storing", §"Flat Lifting", and §"Flat Lowering".

Floats are raw IEEE-754 interchange bits (`BitVec t.width`), the same carrier as
`Silmaril.Wasm.Numerics.FloatValue` and `Execution.Runtime.Value.float`. With this
carrier the reference's `core_f32_reinterpret_i32`, `core_i32_reinterpret_f32`, and
their 64-bit forms are bit casts (`reinterpretIntAsFloat`, `reinterpretFloatAsInt`).

* `CANONICAL_FLOAT32_NAN` and `CANONICAL_FLOAT64_NAN` are `canonicalNaN`.
  `canonicalize_nan32` and `canonicalize_nan64` are `canonicalizeNaN`.
  `decode_i32_as_float` and `decode_i64_as_float` are `decodeFloat`.
* `maybe_scramble_nan32` and `maybe_scramble_nan64` are the relation `ScrambleNaN`.
  With `deterministic := true` (`DETERMINISTIC_PROFILE`), a NaN becomes exactly the
  canonical NaN. With `deterministic := false`, a NaN may become *any* NaN. This is
  what the `CanonicalABI.md` §"Storing" prose permits ("Hosts may instead chose to
  canonicalize to an arbitrary fixed NaN value, or even to the original value of the
  NaN before lifting"). It is a strict superset of the image of the Python
  `random_nan_bits`, which never produces the canonical NaN (it always sets a
  fraction bit below the quiet bit). `RandomNaNBits` states that image exactly.
  `encode_float_as_i32` and `encode_float_as_i64` are `EncodeFloat`.
* `lift_flat` (`F32Type`/`F64Type`) is `liftFloatFlat`. `lower_flat` is
  `LowerFloatFlat`. `load` is `loadFloat`. `store` is `StoreFloat`. The
  deterministic executable choices are `lowerFloatFlatCanonical` and
  `storeFloatCanonical`.
* `convert_i32_to_char` is `convertI32ToChar?` (`none` is a trap), and `char_to_i32`
  is `charToI32`. Chars are Lean `Char`, whose invariant is exactly "Unicode scalar
  value". `liftCharFlat`, `lowerCharFlat`, `loadChar`, and `storeChar` are the
  corresponding `lift_flat`, `lower_flat`, `load`, and `store` cases.

As in `ABI.Memory`, memory helpers allow unaligned access and fail (`none`) out of
bounds. Alignment and pointer-width checks belong to the enclosing adapter. For
`loadChar`, `none` merges an out-of-bounds access and an invalid scalar value, and
both trap in the reference.

**wasmtime** (`a7b4f29`). `crates/wasmtime/src/runtime/component/func/typed.rs`
(`floats!`) lifts and lowers host `f32`/`f64` by `from_bits`/`to_bits`, and
`crates/environ/src/fact/trampoline.rs` (`translate_f32`, `translate_f64`) copies
float bits between components unchanged. wasmtime therefore neither canonicalizes on
lift nor scrambles on lower. Its end-to-end identity on bits is admitted by the
nondeterministic profile, since lift then `ScrambleNaN false` may return the original
NaN (`scrambleNaN_canonicalizeNaN_self` in `FloatChar/Properties`). It is *not* the
deterministic profile. A wasmtime host can also observe non-canonical NaN payloads
that the reference's lift would have erased. wasmtime's `char` lift is
`char::try_from(u32)`. The adapter's inline check in `translate_char` is transcribed
as `wasmtimeCharCheck` and proved equivalent to `convertI32ToChar?` succeeding.

**Integration note.** `ABI.Scalar.Scalar`/`ScalarValue` cover only booleans and
integers, and they are not modified here. The proposed extension adds the cases
`f32 | f64 | char` to `Scalar`, with `width` 32/64/32 and `coreType` generalised
from `IntType` to `NumType`. Float `bits` would be raw bits (lift: `decodeFloat`,
lower: `ScrambleNaN`), and a char's bits would carry the proof
`bits.toNat.isValidChar`, or the value type would become an inductive with a `Char`
case. Lowering then becomes a relation (because of NaN nondeterminism) with the
deterministic function as a witness.

Not modelled: the Python float type itself (the reference's `math.isnan` is the bit
predicate `isNaN` here), and the `latin1+utf16` string machinery that also
uses `char`. No conformance claim beyond the theorems in `FloatChar/Properties` is
made.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

open Silmaril.Wasm.Execution

/-! ## Floating-point bits -/

/-! ## Flat and memory adapters for floats -/

/-! ## Chars -/

end Silmaril.Wasm.Component.ABI
