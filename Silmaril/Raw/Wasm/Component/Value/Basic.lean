module

public import Silmaril.Wasm.Component.Reference.Value.Basic.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Ids
public import Silmaril.Raw.Wasm.Component.ABI.String
public import Silmaril.Raw.Wasm.Component.ABI.Scalar

/-!
# Component-level values

The dynamic values that the canonical ABI lifts from and lowers into core wasm:
the Python values of `lift_flat`/`load` and `lower_flat`/`store` in REF
`definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>;
prose in `CanonicalABI.md`, "Loading"/"Storing"/"Flattening").

`Val` has one constructor per value *shape* rather than one per WIT type:

* `bool`, integers `int k n` (a mathematical `Int` with its `IntKind`; the REF uses
  Python `int`), floats as bit patterns (`f32`/`f64`; NaN choices are made at
  lowering, see `ABI/FloatChar.lean`) and `char` (a Lean `Char`, i.e. a Unicode
  scalar value);
* `string s` for the REF `String = (str, encoding, tagged_code_units)` tuple, see
  `StrVal` below;
* `list`, `record` (also tuples and the despecialized forms), `variant case payload`
  (also enum = no payload, `option`/`result` = cases 0/1), `flags` (one `Bool` per
  label, in label order; REF uses a `dict[str,bool]`), maps as lists of 2-field
  records (REF `MapType` despecializes to a list of tuples);
* handles: `own rep`/`borrow rep` carry the lifted resource representation (REF
  `lift_own`/`lift_borrow`, L1425-1439, return `h.rep`), `stream`/`future` carry the runtime
  end (REF lifts to the `ReadableStreamEnd`/`ReadableFutureEnd` object) and
  `errorContext` the runtime error-context object.

Values are untyped: well-typedness against `WIT.ValType` is a separate relation
(`Value/Typing.lean`). Field and case labels are not stored.

## Deviation D-a: strings remember their source pointer width

The REF `store_string`/`store_string_into_range` (L1533-1551) untags a
`latin1+utf16` count with the tag of the *destination* memory
(`utf16_tag(cx.opts.memory.ptr_type())`, `utf16_tag` at L1331), although
`load_string_from_range` (L1338-1366) kept the count tagged with the *source*
memory's tag when lifted. Between memories of different
pointer width this misreads the count. `StrVal` therefore stores the pointer width
`srcAddr` of the memory the string was lifted from, and `StrVal.retag dst` is the
REF value re-tagged for the destination width; the canonical ABI stores
`s.retag dst` (reproducing the raw REF behaviour is `Quirks.refUtf16TagBug`, deviation D-a).
`retag_self` shows this is the identity between equal widths and `retag_consistent` that it
preserves `StringValue.Consistent`.

Equality: `Val` has decidable equality (hand-written over the nested inductive, so
it reduces in the kernel), and `Val.eqUpToEnc` is structural equality with strings
compared by their text only. It is *stricter* than REF `run_tests.py`
`equal_modulo_string_encoding` (L7-20), which compares variant dicts by payload
only (ignoring the case) and floats with Python `==` (`-0.0 == 0.0`, NaN never
equal); `eqUpToEnc` compares variant case indices and float bit patterns. A port
of `run_tests.py` that needs the REF comparison must define it separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Value

open ABI

/-! ## Integer kinds -/

namespace IntKind

theorem ofScalar?_toScalar (k : IntKind) : ofScalar? k.toScalar = some k := by cases k <;> rfl

theorem width_toScalar (k : IntKind) : k.toScalar.width = k.width := by cases k <;> rfl

theorem signed_toScalar (k : IntKind) : k.toScalar.signed = k.signed := by cases k <;> rfl

example : IntKind.u8.inRange 255 = true := by decide +kernel
example : IntKind.u8.inRange 256 = false := by decide +kernel
example : IntKind.s8.inRange (-128) = true := by decide +kernel
example : IntKind.s8.inRange (-129) = false := by decide +kernel
example : IntKind.s64.inRange (2 ^ 63 - 1) = true := by decide +kernel
example : IntKind.u32.inRange (-1) = false := by decide +kernel

end IntKind

/-! ## Strings (deviation D-a) -/

namespace StrVal

end StrVal

/-! ### Tag arithmetic -/

theorem utf16Tag_eq_two_pow (a : AddrType) : utf16Tag a = 2 ^ tagBit a := by
  cases a <;> rfl

private theorem and_two_pow_ne_zero {x k : Nat} :
    (x &&& 2 ^ k != 0) = x.testBit k := by
  by_cases h : x.testBit k
  · have : x &&& 2 ^ k = 2 ^ k := by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow]
      by_cases hi : k = i
      · subst hi; simp [h]
      · simp [hi]
    rw [this, h]; simp
  · have : x &&& 2 ^ k = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : k = i
      · subst hi; simp [h]
      · simp [hi]
    simp [this, h]

theorem isUtf16Tagged_eq_testBit (a : AddrType) (n : Nat) :
    isUtf16Tagged a n = n.testBit (tagBit a) := by
  unfold isUtf16Tagged; rw [utf16Tag_eq_two_pow]; exact and_two_pow_ne_zero

/-- Untagging then re-tagging with the same width restores a tagged count. -/
theorem tagUtf16_untagUtf16 (a : AddrType) {n : Nat} (h : isUtf16Tagged a n = true) :
    tagUtf16 a (untagUtf16 a n) = n := by
  rw [isUtf16Tagged_eq_testBit] at h
  unfold tagUtf16 untagUtf16; rw [utf16Tag_eq_two_pow]
  generalize tagBit a = k at h ⊢
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : k = i
  · subst hi; simp [h]
  · simp [hi]

theorem isUtf16Tagged_tagUtf16 (a : AddrType) (n : Nat) :
    isUtf16Tagged a (tagUtf16 a n) = true := by
  rw [isUtf16Tagged_eq_testBit]; unfold tagUtf16; rw [utf16Tag_eq_two_pow]
  simp [Nat.testBit_or]

theorem isUtf16Tagged_of_lt (a : AddrType) {n : Nat} (h : n < utf16Tag a) :
    isUtf16Tagged a n = false := by
  rw [isUtf16Tagged_eq_testBit]; rw [utf16Tag_eq_two_pow] at h
  exact Nat.testBit_lt_two_pow h

theorem untagUtf16_tagUtf16 (a : AddrType) {n : Nat} (h : n < utf16Tag a) :
    untagUtf16 a (tagUtf16 a n) = n := by
  unfold tagUtf16 untagUtf16; rw [utf16Tag_eq_two_pow] at h ⊢
  generalize tagBit a = k at h ⊢
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : k = i
  · subst hi; simp [Nat.testBit_lt_two_pow h]
  · simp [hi]

namespace StrVal

/-- Re-tagging for the source width is the identity. (The spec asked for this under
the hypothesis that the untagged count is below the tag; it holds unconditionally.) -/
theorem retag_self (s : StrVal) : s.retag s.srcAddr = s.v := by
  unfold retag
  split
  · next h => rw [tagUtf16_untagUtf16 _ h.2]
  · rfl

/-- Re-tagging preserves consistency whenever the untagged count fits below the
destination tag. -/
theorem retag_consistent (s : StrVal) (dst : AddrType) (hc : s.v.Consistent s.srcAddr)
    (hlt : s.untaggedCount < utf16Tag dst) : (s.retag dst).Consistent dst := by
  rcases s with ⟨⟨str, enc, t⟩, src⟩
  unfold untaggedCount at hlt
  unfold retag
  cases enc with
  | utf8 => exact hc
  | utf16 => exact hc
  | latin1Utf16 =>
    simp only [StringValue.Consistent] at hc
    by_cases ht : isUtf16Tagged src t = true
    · simp only [ht, ite_true, true_and] at hc hlt ⊢
      simp only [StringValue.Consistent, isUtf16Tagged_tagUtf16, ite_true,
        untagUtf16_tagUtf16 dst hlt]
      exact hc
    · simp only [ht, ite_false, and_false, Bool.false_eq_true] at hc hlt ⊢
      simp only [StringValue.Consistent, isUtf16Tagged_of_lt dst hlt, Bool.false_eq_true,
        ite_false]
      exact hc

/-- A UTF-16-tagged `latin1+utf16` count of 3 lifted from a 32-bit memory has its tag
bit moved from bit 31 to bit 63 for a 64-bit destination. -/
theorem retag_i32_i64_example :
    (StrVal.mk ⟨"abc", .latin1Utf16, 3 + 2 ^ 31⟩ .i32).retag .i64 =
      ⟨"abc", .latin1Utf16, 3 + 2 ^ 63⟩ := by decide +kernel

example : (StrVal.mk ⟨"abc", .latin1Utf16, 3 + 2 ^ 31⟩ .i32).retag .i32 =
    ⟨"abc", .latin1Utf16, 3 + 2 ^ 31⟩ := by decide +kernel
example : (StrVal.mk ⟨"abc", .latin1Utf16, 3⟩ .i32).retag .i64 =
    ⟨"abc", .latin1Utf16, 3⟩ := by decide +kernel
example : (StrVal.mk ⟨"abc", .latin1Utf16, 3 + 2 ^ 63⟩ .i64).retag .i32 =
    ⟨"abc", .latin1Utf16, 3 + 2 ^ 31⟩ := by decide +kernel

end StrVal

/-! ## Values -/

namespace Val

/-! ### Decidable equality

`deriving DecidableEq` does not support nested inductives, so equality is decided
by a structurally recursive Boolean test `beq` together with `beq_iff`. -/

example : ofScalar ⟨.u8, 255#8⟩ = .int .u8 255 := by decide +kernel
example : ofScalar ⟨.s8, 255#8⟩ = .int .s8 (-1) := by decide +kernel
example : ofScalar ⟨.bool, 1#1⟩ = .bool true := by decide +kernel

/-! ### Tests -/

private def hiUtf8 : Val := .string ⟨⟨"hi", .utf8, 2⟩, .i32⟩
private def hiUtf16 : Val := .string ⟨⟨"hi", .utf16, 2⟩, .i64⟩

example : eqUpToEnc hiUtf8 hiUtf16 = true := by decide +kernel
example : hiUtf8 ≠ hiUtf16 := by decide +kernel
example : eqUpToEnc (.list [hiUtf8, .u32 3]) (.list [hiUtf16, .u32 3]) = true := by
  decide +kernel
example : eqUpToEnc (.list [hiUtf8, .u32 3]) (.list [hiUtf16, .u32 4]) = false := by
  decide +kernel

example : Val.record [.u32 1, .variant 1 (some (.list [.bool true, .char 'x']))] =
    Val.record [.u32 1, .variant 1 (some (.list [.bool true, .char 'x']))] := by decide +kernel
example : Val.record [.u32 1, .variant 1 (some (.list [.bool true, .char 'x']))] ≠
    Val.record [.u32 1, .variant 1 (some (.list [.bool false, .char 'x']))] := by
  decide +kernel
example : Val.variant 0 none ≠ Val.variant 0 (some (.f32 0#32)) := by decide +kernel
example : Val.list [.own 1, .stream ⟨2⟩] ≠ Val.list [.own 1, .future ⟨2⟩] := by
  decide +kernel
example : Val.flags [true, false] = Val.flags [true, false] := by decide +kernel

end Val

end Silmaril.Wasm.Component.Value
