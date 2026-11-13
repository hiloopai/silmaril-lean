module

public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs

public import Silmaril.Raw.Wasm.Component.Value.Basic
public import Silmaril.Raw.Wasm.Component.ABI.Despecialize
public import Silmaril.Raw.Wasm.Component.ABI.FloatChar

/-!
# Typing of component-level values

`Val.HasType v t` says that the component value `v` (`Value/Basic.lean`) is a value of the
closed WIT type `t`. It is a pointer-width-independent over-approximation of the Python
values that REF `lift_flat`/`load` can produce at type `t` (see the list-length and
handle caveats below), following `definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>):
`load` (L1256), `load_string_from_range` (L1338), `load_list` (L1376), `load_record`
(L1395), `load_variant` (L1403), `load_flags` (L1414), `lift_flat` (L1869). As in the REF,
the specialized types are typed through `despecialize` (L1101):

* `bool`; integers `int k n` with `IntKind.ofPrimitive p = some k` and `k.inRange n`;
  `f32`/`f64` with any bit pattern (NaN canonicality is the separate predicate
  `Val.IsNanCanonical`; see `Val.canonicalizeNaN`); `char` with any Lean `Char` (a Unicode
  scalar value by construction);
* `string s` with `s.Valid`: the code-unit hint is consistent with the text for the
  source pointer width (`ABI.StringValue.Consistent`) and the untagged byte length is at
  most `ABI.maxStringByteLength` (the `load_string_from_range` trap bound);
* `list` of well-typed elements; `fixed-list` with exactly `n` well-typed elements
  (represented by `Val.list`); `record` pointwise (`HasFields`); `variant c p` with
  `c < cases.length` and a payload exactly when the case has one (`HasCase`, `HasOpt`);
  `flags` with one `Bool` per label;
* `tuple`, `enum`, `option`, `result` and `map` hold of `v` iff `v` has the
  despecialized type;
* `own`/`borrow` with any representation (resource identity is not part of the value;
  handles are typed by lift/lower), `stream`/`future` with any end id,
  `error-context` with any id.

`Val.typeCheck?` is the executable check (structurally recursive, so it reduces in the
kernel) and `typeCheck?_iff` proves it equivalent to `HasType`; the `Decidable` instance
is derived from it. `Val.canonicalizeNaN` canonicalizes every float
(`ABI.canonicalizeNaN`, REF `canonicalize_nan32/64`, L1294–1305); its properties are in
`Value/Typing/Properties.lean`.

Not modelled or claimed: no well-formedness of the type itself is assumed
(`ValType.WellFormedCM` is separate), the store-side contents of handles and async ends
are not checked (REF `lift_own`/`lift_borrow` L1425/L1433 also check the handle's resource
type and `lift_stream`/`lift_future` L1441/L1444 the element type), and nothing is proved
here about lift/lower producing typed values. `list` and `map` lengths are unbounded,
unlike the string bound: REF `load_list_from_range` (L1384) traps when
`length * elem_size(elem_type, ptr_type) > MAX_LIST_BYTE_LENGTH = 2^28-1` (L1373), a bound
that depends on the pointer width through `elem_size`, so a lifted list additionally
satisfies it. Conversely `HasType` alone does not discharge REF `store_list_into_range`'s
`assert(byte_length <= REALLOC_I32_MAX)` (L1691); by deviation D-f that assert is a
precondition which callers lowering a value must establish separately.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Value

universe u

open ABI

/-! ## Integer kinds and primitives -/

namespace IntKind

theorem ofPrimitive_toPrimitive (k : IntKind) : ofPrimitive k.toPrimitive = some k := by
  cases k <;> rfl

theorem toPrimitive_of_ofPrimitive {p : WIT.Primitive} {k : IntKind}
    (h : ofPrimitive p = some k) : k.toPrimitive = p := by
  cases p <;> simp only [ofPrimitive, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

theorem ofPrimitive_eq_some_iff {p : WIT.Primitive} {k : IntKind} :
    ofPrimitive p = some k ↔ k.toPrimitive = p := by
  constructor
  · exact toPrimitive_of_ofPrimitive
  · rintro rfl; exact ofPrimitive_toPrimitive k

end IntKind

/-! ## Valid strings -/

namespace StrVal

end StrVal

namespace Val

variable {R : Type u}

/-! ## Value constructors -/

/-! ## The typing relation -/

/-! ## The executable check -/

/-! ## Correctness of the check, case by case -/

/-! ## `typeCheck?` decides `HasType` -/

/-! ## NaN canonicalization -/

/-! ## Tests -/

/-- `option u8` accepts `some 7`. -/
theorem typeCheck?_option_u8_some7 :
    typeCheck? (.option (.prim .u8) : WIT.ClosedType Nat) (.variant 1 (some (.int .u8 7))) =
      true := by decide +kernel
example : HasType (.variant 1 (some (.int .u8 7))) (.option (.prim .u8) : WIT.ClosedType Nat) :=
  by decide +kernel
example : typeCheck? (.option (.prim .u8) : WIT.ClosedType Nat)
    (.variant 1 (some (.int .u8 256))) = false := by decide +kernel
example : typeCheck? (.option (.prim .u8) : WIT.ClosedType Nat) (.variant 0 none) = true := by
  decide +kernel

/-- Record typing. -/
theorem hasType_record_example :
    HasType (.record [.s32 (-3), .string ⟨⟨"hi", .utf8, 2⟩, .i32⟩,
      .list [.bool true, .bool false]]) testPointType := by decide +kernel
/-- Record typing: wrong arity, wrong field type and an inconsistent string hint fail. -/
example : ¬ HasType (.record [.s32 (-3), .string ⟨⟨"hi", .utf8, 2⟩, .i32⟩])
    testPointType := by decide +kernel
example : ¬ HasType (.record [.u32 3, .string ⟨⟨"hi", .utf8, 2⟩, .i32⟩, .list []])
    testPointType := by decide +kernel
example : ¬ HasType (.record [.s32 3, .string ⟨⟨"hi", .utf8, 3⟩, .i32⟩, .list []])
    testPointType := by decide +kernel

/-- `char`: an integer is not a char (a `Val.char` is always a scalar value). -/
theorem typeCheck?_char_u32_neg :
    typeCheck? (.prim .char : WIT.ClosedType Nat) (.u32 0x110000) = false := by
  decide +kernel
example : typeCheck? (.prim .char : WIT.ClosedType Nat) (.char 'x') = true := by decide +kernel
/-- `variant`: a case index out of range, or a payload on a payload-free case, fails. -/
theorem typeCheck?_variant_out_of_range :
    typeCheck? (.variant [("a", none), ("b", some (.prim .u8))] : WIT.ClosedType Nat)
      (.variant 2 none) = false := by decide +kernel
example : typeCheck? (.variant [("a", none), ("b", some (.prim .u8))] : WIT.ClosedType Nat)
    (.variant 0 (some (.int .u8 1))) = false := by decide +kernel
example : typeCheck? (.variant [("a", none), ("b", some (.prim .u8))] : WIT.ClosedType Nat)
    (.variant 1 (some (.int .u8 1))) = true := by decide +kernel
example : typeCheck? (.enum ["a", "b"] : WIT.ClosedType Nat) (.variant 2 none) = false := by
  decide +kernel
example : typeCheck? (.result (some (.prim .u32)) none : WIT.ClosedType Nat)
    (.variant 1 none) = true := by decide +kernel
example : typeCheck? (.tuple [.prim .u8, .prim .char] : WIT.ClosedType Nat)
    (.record [.int .u8 1, .char 'c']) = true := by decide +kernel
example : typeCheck? (.map .string (.prim .u64) : WIT.ClosedType Nat)
    (.list [.record [.string ⟨⟨"k", .utf8, 1⟩, .i32⟩, .int .u64 5]]) = true := by
  decide +kernel
example : typeCheck? (.fixedList (.prim .u8) 2 : WIT.ClosedType Nat)
    (.list [.int .u8 1]) = false := by decide +kernel
example : typeCheck? (.flags ["a", "b"] : WIT.ClosedType Nat) (.flags [true, false]) = true :=
  by decide +kernel

example : canonicalizeNaN (.list [.f32 0xffc00000#32, .f32 1#32]) =
    .list [.f32 0x7fc00000#32, .f32 1#32] := by decide +kernel
example : ¬ IsNanCanonical (.variant 0 (some (.f64 0xfff8000000000001#64))) := by decide +kernel

end Val

end Silmaril.Wasm.Component.Value
