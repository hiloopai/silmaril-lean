module

public import Silmaril.Wasm.Component.Reference.Runtime.Ids.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Scalar.Defs

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

/-- The eight WIT integer types. -/
inductive IntKind where
  | u8 | u16 | u32 | u64 | s8 | s16 | s32 | s64
  deriving DecidableEq, Repr, Hashable, Inhabited

namespace IntKind

/-- Bit width. -/
def width : IntKind → Nat
  | .u8 | .s8 => 8
  | .u16 | .s16 => 16
  | .u32 | .s32 => 32
  | .u64 | .s64 => 64

/-- Whether the kind is signed. -/
def signed : IntKind → Bool
  | .s8 | .s16 | .s32 | .s64 => true
  | _ => false

/-- Smallest representable value. -/
def minValue (k : IntKind) : Int := if k.signed then -(2 ^ (k.width - 1) : Int) else 0

/-- One more than the largest representable value. -/
def bound (k : IntKind) : Int := if k.signed then (2 ^ (k.width - 1) : Int) else 2 ^ k.width

/-- `n` is a value of this integer type. -/
def inRange (k : IntKind) (n : Int) : Bool := decide (k.minValue ≤ n) && decide (n < k.bound)

/-- The corresponding `ABI.Scalar`. -/
def toScalar : IntKind → Scalar
  | .u8 => .u8 | .u16 => .u16 | .u32 => .u32 | .u64 => .u64
  | .s8 => .s8 | .s16 => .s16 | .s32 => .s32 | .s64 => .s64

/-- The integer kind of an `ABI.Scalar` (`none` for `bool`). -/
def ofScalar? : Scalar → Option IntKind
  | .bool => none
  | .u8 => some .u8 | .u16 => some .u16 | .u32 => some .u32 | .u64 => some .u64
  | .s8 => some .s8 | .s16 => some .s16 | .s32 => some .s32 | .s64 => some .s64

end IntKind

/-! ## Strings (deviation D-a) -/

/-- A lifted string: the REF `String` tuple plus the pointer width of the memory it
was lifted from (deviation D-a). -/
structure StrVal where
  /-- The REF lifted string `(str, encoding, tagged_code_units)`. -/
  v : StringValue
  /-- Pointer width of the memory the string was lifted from (D-a). -/
  srcAddr : AddrType
  deriving DecidableEq, Repr

namespace StrVal

/-- The code-unit count without the `latin1+utf16` UTF-16 tag of the source memory. -/
def untaggedCount (s : StrVal) : Nat :=
  if s.v.encoding = .latin1Utf16 ∧ isUtf16Tagged s.srcAddr s.v.taggedCodeUnits then
    untagUtf16 s.srcAddr s.v.taggedCodeUnits
  else s.v.taggedCodeUnits

/-- The REF value re-tagged for a destination memory of pointer width `dst`: a
UTF-16-tagged `latin1+utf16` count moves its tag bit to `dst`'s tag position. -/
def retag (s : StrVal) (dst : AddrType) : StringValue :=
  if s.v.encoding = .latin1Utf16 ∧ isUtf16Tagged s.srcAddr s.v.taggedCodeUnits then
    { s.v with taggedCodeUnits := tagUtf16 dst (untagUtf16 s.srcAddr s.v.taggedCodeUnits) }
  else s.v

end StrVal

/-! ### Tag arithmetic -/

/-- The bit position of the UTF-16 tag: `ptr_size(ptr_type) * 8 - 1`. -/
def tagBit : AddrType → Nat
  | .i32 => 31
  | .i64 => 63

namespace StrVal

end StrVal

/-! ## Values -/

/-- A component-level value (see the module docstring for the encoding of each
WIT type). -/
inductive Val where
  | bool (b : Bool)
  | int (k : IntKind) (n : Int)
  | f32 (bits : BitVec 32)
  | f64 (bits : BitVec 64)
  | char (c : Char)
  | string (s : StrVal)
  | list (vs : List Val)
  | record (fields : List Val)
  | variant (case : Nat) (payload : Option Val)
  | flags (bits : List Bool)
  | own (rep : Nat)
  | borrow (rep : Nat)
  | stream (e : Runtime.EndId)
  | future (e : Runtime.EndId)
  | errorContext (x : Runtime.ErrCtxId)
  deriving Repr, Inhabited

namespace Val

/-! ### Decidable equality

`deriving DecidableEq` does not support nested inductives, so equality is decided
by a structurally recursive Boolean test `beq` together with `beq_iff`. -/

mutual
/-- Structural Boolean equality (reduces in the kernel). -/
def beq : Val → Val → Bool
  | .bool a, .bool b => decide (a = b)
  | .int k n, .int k' n' => decide (k = k') && decide (n = n')
  | .f32 a, .f32 b => decide (a = b)
  | .f64 a, .f64 b => decide (a = b)
  | .char a, .char b => decide (a = b)
  | .string a, .string b => decide (a = b)
  | .list a, .list b => beqList a b
  | .record a, .record b => beqList a b
  | .variant c p, .variant c' p' => decide (c = c') && beqOption p p'
  | .flags a, .flags b => decide (a = b)
  | .own a, .own b => decide (a = b)
  | .borrow a, .borrow b => decide (a = b)
  | .stream a, .stream b => decide (a = b)
  | .future a, .future b => decide (a = b)
  | .errorContext a, .errorContext b => decide (a = b)
  | _, _ => false

/-- `beq` on lists. -/
def beqList : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false

/-- `beq` on options. -/
def beqOption : Option Val → Option Val → Bool
  | none, none => true
  | some x, some y => beq x y
  | _, _ => false
end

mutual
theorem beq_iff (x y : Val) : beq x y = true ↔ x = y := by
  cases x <;> cases y <;>
    simp only [beq, reduceCtorEq, Bool.false_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      Val.bool.injEq, Val.int.injEq, Val.f32.injEq, Val.f64.injEq, Val.char.injEq,
      Val.string.injEq, Val.list.injEq, Val.record.injEq, Val.variant.injEq, Val.flags.injEq,
      Val.own.injEq, Val.borrow.injEq, Val.stream.injEq, Val.future.injEq,
      Val.errorContext.injEq]
  case list.list a b => exact beqList_iff a b
  case record.record a b => exact beqList_iff a b
  case variant.variant c p c' p' => rw [beqOption_iff p p']

theorem beqList_iff (xs ys : List Val) : beqList xs ys = true ↔ xs = ys := by
  cases xs <;> cases ys <;>
    simp only [beqList, reduceCtorEq, List.cons.injEq, Bool.and_eq_true, Bool.false_eq_true]
  case cons.cons a as b bs => rw [beq_iff a b, beqList_iff as bs]

theorem beqOption_iff (x y : Option Val) : beqOption x y = true ↔ x = y := by
  cases x <;> cases y <;>
    simp only [beqOption, reduceCtorEq, Option.some.injEq, Bool.false_eq_true]
  case some.some a b => exact beq_iff a b
end

instance : DecidableEq Val := fun x y => decidable_of_iff _ (beq_iff x y)

mutual
/-- Structural equality with strings compared by `s.v.str` only (ignoring encoding,
code-unit hint and `srcAddr`). Stricter than REF `run_tests.py`
`equal_modulo_string_encoding`: variant case indices are compared, and floats are
compared bitwise (`+0 ≠ -0`; a NaN equals itself when the bits match), whereas the
REF ignores variant labels and uses Python float `==`. -/
def eqUpToEnc : Val → Val → Bool
  | .string a, .string b => a.v.str == b.v.str
  | .list a, .list b => eqUpToEncList a b
  | .record a, .record b => eqUpToEncList a b
  | .variant c p, .variant c' p' => c == c' && eqUpToEncOption p p'
  | x, y => decide (x = y)

/-- `eqUpToEnc` on lists. -/
def eqUpToEncList : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqUpToEnc x y && eqUpToEncList xs ys
  | _, _ => false

/-- `eqUpToEnc` on options. -/
def eqUpToEncOption : Option Val → Option Val → Bool
  | none, none => true
  | some x, some y => eqUpToEnc x y
  | _, _ => false
end

/-- A `u32` value. -/
def u32 (n : Nat) : Val := .int .u32 n

/-- An `s32` value. -/
def s32 (n : Int) : Val := .int .s32 n

/-- An `option` value: `none` is case 0, `some v` is case 1. -/
def option (v : Option Val) : Val :=
  match v with
  | none => .variant 0 none
  | some x => .variant 1 (some x)

/-- A `result` value: `ok` is case 0, `error` is case 1. -/
def result (v : Sum (Option Val) (Option Val)) : Val :=
  match v with
  | .inl p => .variant 0 p
  | .inr p => .variant 1 p

/-- The component value of a canonical boolean/integer scalar (`ABI/Scalar.lean`):
booleans by their nonzero bit, integers by their mathematical value. -/
def ofScalar (v : ScalarValue) : Val :=
  match IntKind.ofScalar? v.type with
  | none => .bool (v.bits.toNat != 0)
  | some k => .int k v.toInt

/-! ### Tests -/

end Val

end Silmaril.Wasm.Component.Value
