module

public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Load
public import Silmaril.Raw.Wasm.Component.Canon.Store
public import Silmaril.Raw.Wasm.Component.ABI.Flatten
public import Silmaril.Raw.Wasm.Component.ABI.Calling
public import Silmaril.Raw.Wasm.Component.Async.Codes

/-!
# Flat lifting and lowering, and spilling of function arguments and results

The flat half of the Canonical ABI of REF `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
as specification programs in `P E σ` over closed types `WIT.ClosedType RtId`:

| Lean | REF (lines) |
| --- | --- |
| `FlatCursor`, `FlatCursor.next`, `FlatCursor.nextN` | `CoreValueIter` (L1850-1867) |
| `liftFlat lim q cx vi t` (via `liftFlatAt`) | `lift_flat` (L1869-1892) |
| `liftFlatPrim` | scalar arms of `lift_flat`, `lift_flat_unsigned`/`_signed` (L1894-1905) |
| `liftFlatPrim` (`.string`) | `lift_flat_string` (L1907-1910) |
| `liftFlatAt` (`list`/`fixedList`/`map`), `liftFlatN` | `lift_flat_list` (L1912-1920) |
| `liftFlatFields`, `liftFlatTypes` | `lift_flat_record` (L1922-1926) |
| `liftFlatVariantWith`, `liftFlatCaseAt`, `coerceLiftSlots` | `lift_flat_variant` (L1928-1950) |
| `coerceLiftFlat` (reused, `Canon/Scalar.lean`) | `CoerceValueIter.next`, `wrap_i64_to_i32` |
| `liftFlatAt` (`flags`) | `lift_flat_flags` (L1956-1959) |
| `lowerFlat lim q cx v t` (via `lowerFlatAt`) | `lower_flat` (L1963-1986) |
| `lowerFlatPrim` | scalar arms, `lower_flat_signed` (L1988-1991) |
| `lowerFlatPrim` (`.string`) | `lower_flat_string` (L1993-1995) |
| `lowerFlatAt` (`list`/`fixedList`/`map`) | `lower_flat_list` (L1997-2005) |
| `lowerFlatFields`, `lowerFlatTypes` | `lower_flat_record` (L2007-2011) |
| `lowerFlatVariantWith`, `lowerFlatCase`, `coerceLowerSlots` | `lower_flat_variant` (L2013-2032) |
| `lowerFlatAt` (`flags`) | `lower_flat_flags` (L2034-2036) |
| `liftFlatValues lim q cx max vi ts` | `lift_flat_values` (L2040-2049) |
| `lowerFlatValues lim q cx max vs ts outParam` | `lower_flat_values` (L2051-2070) |
| `unpackCallbackResult` (`Async.unpackCallbackResult`) | `unpack_callback_result` (L2153-2159) |
| `ABI.maxFlatParams`/`maxFlatAsyncParams`/`maxFlatResults` (reused) | `MAX_FLAT_*` (L1765-1767) |

Flat types are the `ABI.flatten p` (REF `flatten_type`, with `ABI.variantPayload` the
joined payload of `flatten_variant` without its `i32` discriminant, and `ABI.flattenTypes`
REF `flatten_types`), sizes and alignments are `ABI.layout p`, with `p` the pointer width of
`cx`'s memory (`ptrType cx`, D-g), read once per entry point as in `Canon/Load.lean`.

## The cursor

`FlatCursor` is REF `CoreValueIter`: the list of flat values and the position `pos` of the
next one (the representation stored by `Runtime.Caller.lower`, whose flat-argument iterator
is shared between `lift_flat_values` of the arguments and the out-parameter of
`lower_flat_values` of the results). `FlatCursor.next t` returns the value at `pos` and the
advanced cursor. The REF asserts on the value's core type and range are preconditions (D-f):
the value's bits are read as they are (`v.bits.toNat` for integers, the low 32/64 bits for
floats); reading past the end is an `internal` trap (REF `IndexError`).

## Structure

`liftFlatAt lim q cx p t vi` and `lowerFlatAt lim q cx p v t` are defined by **structural**
recursion on `t` (mutually with the record/tuple/case helpers), as `loadAt` in
`Canon/Load.lean`, so they reduce in the kernel. Specialized types are lifted and lowered as
REF does on their despecialization (L1101-1108) without rebuilding it: `tuple` as a record,
`enum` as a variant without payloads, `option t` as `[none, some t]`, `result ok err` as
`[ok, err]` and `map k v` as a list of records `{"0": k, "1": v}` (`ABI.mapEntryFields`).
Lists (and maps) spill to memory through the entry points of `Canon/Load.lean` and
`Canon/Store.lean` (`loadListFromRangeWith`, `storeListIntoRange`); strings through
`loadStringFromRange`/`storeStringIntoRange`.

## Deviations and non-claims

* D-f: every REF assert is a precondition: the core type and range of each flat value, the
  flags label count `0 < n <= 32`, `maybe_length == len(v)` for fixed lists, `match_case`
  and the `have == want` assert of the variant coercion tables (outside the tables the value
  is passed unchanged, as `coerceLiftFlat`/`coerceLower` do). A value whose shape does not
  match the type reaches `internal` (`flatMismatch`), as in `Canon/Store.lean`.
* `lift_flat_variant`: REF reads the payload slots through `CoerceValueIter` while lifting the
  case's payload and then reads the remaining slots. Here all joined payload slots are read
  first (`FlatCursor.nextN`), coerced against the case's own flat types (`coerceLiftSlots`,
  i.e. the `want` argument REF's inner `lift_flat` passes, which is `flatten_type(c.t)` in
  order), and the payload is lifted from a fresh cursor over the coerced values. Reading the
  iterator has no effect on the store, so this differs from REF only when the flat list is
  too short (a REF `IndexError`, here `internal` before any payload effect).
* `lower_flat_variant`: a variant value carries its case index into the type it is lowered at
  (as in `Canon/Store.lean`; `matchCase`/`storeMatched` cover lowering at a different
  variant type). An index out of range is a shape mismatch. Padding slots are REF's integer
  `0`, here the zero bit pattern of the slot's joined core type (`Value.zero`), so every
  lowered flat value has the core type `ABI.flatten` prescribes.
* Floats: lifting canonicalizes NaNs (REF `canonicalize_nan32/64`), lowering issues the C7
  choice through `lowerFloat` (REF `maybe_scramble_nan32/64`). A NaN `f32`/`f64` payload of a
  variant whose joined slot is an integer is scrambled twice (`coerceLower` re-encodes it),
  exactly as REF.
* `lift_flat_values`/`lower_flat_values` spill when `len(flatten_types(ts)) > max_flat`: the
  pointer is read from `vi` (lift), obtained from `cx.allocate(alignment, elem_size)` of the
  tuple type (lower, returned as the single flat value), or read from the out-parameter
  cursor (lower, returning `[]`); then `trap_if` misaligned (`unalignedPointer`) and out of
  bounds (`outOfBounds`), in REF order, and the tuple is loaded (`loadTypesAt`, the fields of
  `load(cx, ptr, TupleType(ts))`) or stored (`store` at `tuple ts`). The advanced
  out-parameter cursor is not returned (REF mutates the shared iterator, but no caller reads
  it afterwards).
* `unpackCallbackResult` traps `unsupportedCallbackCode` on a code above `CallbackCode.MAX`;
  REF's asserts `packed < 2**32` and `Table.MAX_LENGTH < 2**28` are preconditions.
* Proved here: `P.Inv` lemmas for every program (under `LoadPres I` for lifting and
  `StorePres I` for lowering); kernel-checked examples of `unpackCallbackResult`, one
  `option<u8>` lift and one joined-slot variant lower. Nothing about the
  results (flat types of lowered values, lift/lower round trips) is proved here; those are
  in `Canon/Properties/Flat.lean`, `Canon/Properties/FlatMem.lean` and `Tests/Values.lean`, and no
  conformance test is ported here. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## `CoreValueIter` -/

namespace FlatCursor

end FlatCursor

/-! ## Flat values -/

/-! ## Lifting: non-recursive building blocks -/

/-! ## Lifting -/

/-! ## Lowering: non-recursive building blocks -/

/-! ## Lowering -/

/-! ## `unpack_callback_result` -/

/-! ## Unfolding equations of the entry points -/

section Equations

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)

theorem liftFlatAt_prim (prim : WIT.Primitive) (vi : FlatCursor) :
    (liftFlatAt lim q cx p (.prim prim) vi : P E σ _) = liftFlatPrim lim q cx p prim vi := by
  rw [liftFlatAt]

theorem lowerFlatAt_prim (pt : WIT.Primitive) (v : Val) :
    (lowerFlatAt lim q cx p v (.prim pt) : P E σ _) = lowerFlatPrim lim q cx p pt v := by
  rw [lowerFlatAt]

end Equations

/-! ## Invariant preservation -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem liftFlat (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vi : FlatCursor) (t : WIT.ClosedType RtId) :
    P.Inv I (Canon.liftFlat lim q cx vi t : P E σ _) :=
  bind (ptrType cx) fun p => liftFlatAt h lim q cx p t vi

theorem lowerFlat (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (v : Val) (t : WIT.ClosedType RtId) :
    P.Inv I (Canon.lowerFlat lim q cx v t : P E σ _) :=
  bind (ptrType cx) fun p => lowerFlatAt h lim q cx p v t

end P.Inv

/-! ## Examples -/

section Examples

/-- `unpack_callback_result(0x22)`: `WAIT` on waitable set 2. -/
example : (unpackCallbackResult 0x22 : P E σ _) = pure (.wait, 2) := by
  rw [unpackCallbackResult, show Async.unpackCallbackResult 0x22 = some (.wait, 2) by decide]
  rfl

/-- `unpack_callback_result(0x13)`: code 3 is unsupported. -/
example : (unpackCallbackResult 0x13 : P E σ _) = trap .unsupportedCallbackCode := by
  rw [unpackCallbackResult, show Async.unpackCallbackResult 0x13 = none by decide]
  rfl

/-- `CoreValueIter.next` returns the value at the current position. -/
example : (FlatCursor.next ⟨[i32Flat 7, i32Flat 8], 1⟩ (.int .i32) : P E σ _) =
    pure (i32Flat 8, ⟨[i32Flat 7, i32Flat 8], 2⟩) := rfl

/-- `flatten` of `option<u8>`: an `i32` discriminant followed by the payload's own `i32` slot
(no join widening). -/
example : flatten (Resource := RtId) .i32 (.option (.prim .u8)) = [.int .i32, .int .i32] := by
  decide +kernel

/-- The `variant { a(f32), b(u64) }` payload slot is joined to `i64`. -/
example : variantPayload (flattenCases (Resource := RtId) .i32
    [("a", some (.prim .f32)), ("b", some (.prim .u64))]) = [.int .i64] := by
  decide +kernel

/-- `lift_flat_variant`'s coercion of an `i64` slot to the `f32` case payload. -/
example : coerceLiftSlots [.int .i64] [.float .f32] [⟨.int .i64, 0x3f800000#64⟩] =
    [.float .f32 0x3f800000#32] := by decide

/-- `lift_flat` of `option<u8>` from `[1, 256]`: case 1, payload truncated to `0`, both slots
consumed (reduces by `rfl`; the well-founded `ABI.flatten` needs `with_unfolding_all`). -/
example (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) :
    (liftFlatAt lim q cx .i32 (.option (.prim .u8)) ⟨[i32Flat 1, i32Flat 256], 0⟩ : P E σ _) =
      pure (.variant 1 (some (.int .u8 0)), ⟨[i32Flat 1, i32Flat 256], 2⟩) := by
  with_unfolding_all rfl

/-- `lower_flat` of case `a(1.0f)` of `variant { a(f32), b(u64) }`: the `f32` payload is
re-encoded into the joined `i64` slot (no C7 choice for a non-NaN). -/
example (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) :
    (lowerFlatAt lim q cx .i32 (.variant 0 (some (.f32 0x3f800000#32)))
      (.variant [("a", some (.prim .f32)), ("b", some (.prim .u64))]) : P E σ _) =
      pure [i32Flat 0, ⟨.int .i64, 0x3f800000#64⟩] := by
  with_unfolding_all rfl

end Examples

end Silmaril.Wasm.Component.Canon
