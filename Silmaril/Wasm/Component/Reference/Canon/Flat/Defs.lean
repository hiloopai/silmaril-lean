module

public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Calling.Defs
public import Silmaril.Wasm.Component.Reference.Async.Codes.Defs

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

/-- REF `CoreValueIter` (L1850-1867): the flat values and the index of the next one. -/
structure FlatCursor where
  /-- REF `values`. -/
  values : List FlatValue
  /-- REF `i`. -/
  pos : Nat := 0
  deriving DecidableEq, Repr

namespace FlatCursor

/-- REF `CoreValueIter(vs)`. -/
def ofList (vs : List FlatValue) : FlatCursor := ⟨vs, 0⟩

/-- REF `CoreValueIter.next(t)`: the value at `pos`, and the cursor advanced by one. The core
type `t` is only asserted by REF (D-f) and is not checked; past the end is `internal`. -/
def next (vi : FlatCursor) (_t : CoreType) : P E σ (FlatValue × FlatCursor) :=
  match vi.values[vi.pos]? with
  | some v => pure (v, { vi with pos := vi.pos + 1 })
  | none => internal "CoreValueIter.next: no more flat values"

/-- `ts.length` successive `next` calls with the core types `ts`. -/
def nextN (vi : FlatCursor) : List CoreType → P E σ (List FlatValue × FlatCursor)
  | [] => pure ([], vi)
  | t :: ts => do
    let (v, vi) ← vi.next t
    let (vs, vi) ← nextN vi ts
    return (v :: vs, vi)

end FlatCursor

/-! ## Flat values -/

/-- A pointer-sized flat value (`i32` or `i64` for pointer width `p`). -/
def ptrFlat (p : AddrType) (n : Nat) : FlatValue := ⟨pointerType p, BitVec.ofNat _ n⟩

/-- An `i32` flat value holding `n mod 2^32`. -/
def i32Flat (n : Nat) : FlatValue := .int .i32 (BitVec.ofNat 32 n)

/-- A flat value's bits as an unsigned number (REF core integers are non-negative ints). -/
def flatNat (v : FlatValue) : Nat := v.bits.toNat

/-- A value whose shape does not match the type it is lowered at (D-f; unreachable for
well-typed values). -/
def flatMismatch {α : Type} : P E σ α := internal "lower_flat: value does not match type"

/-- The flat types of the payload of case `i` of `cases` (REF `flatten_type(c.t)`, empty for
a case without payload or past the end). -/
def caseFlat (p : AddrType) (cases : List (String × Option (WIT.ClosedType RtId))) (i : Nat) :
    List CoreType :=
  match cases[i]? with
  | some (_, t) => flattenOption p t
  | none => []

/-! ## Lifting: non-recursive building blocks -/

/-- The scalar and string arms of REF `lift_flat` (L1869-1892) at primitive `prim`:
`convert_int_to_bool(vi.next('i32'))`, `lift_flat_unsigned`/`lift_flat_signed` (`liftFlatInt`,
L1894-1905), `canonicalize_nan32/64(vi.next('f32'/'f64'))`, `convert_i32_to_char` (trap
`invalidChar`) and `lift_flat_string` (L1907-1910: pointer and packed length, both of the
pointer type, then `load_string_from_range`). -/
def liftFlatPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (prim : WIT.Primitive) (vi : FlatCursor) : P E σ (Val × FlatCursor) :=
  match prim with
  | .bool => do
    let (v, vi) ← vi.next (.int .i32)
    return (.bool (liftFlatBool v), vi)
  | .f32 => do
    let (v, vi) ← vi.next (.float .f32)
    return (.f32 (ABI.canonicalizeNaN .f32 (wrapI64ToI32 v)), vi)
  | .f64 => do
    let (v, vi) ← vi.next (.float .f64)
    return (.f64 (ABI.canonicalizeNaN .f64 (flatBits64 v)), vi)
  | .char => do
    let (v, vi) ← vi.next (.int .i32)
    return (.char (← convertI32ToChar (wrapI64ToI32 v)), vi)
  | .string => do
    let (ptr, vi) ← vi.next (pointerType p)
    let (len, vi) ← vi.next (pointerType p)
    return (.string (← loadStringFromRange lim q cx (flatNat ptr) (flatNat len)), vi)
  | .u8 | .u16 | .u32 | .u64 | .s8 | .s16 | .s32 | .s64 =>
    match IntKind.ofPrimitive prim with
    | some k => do
      let (v, vi) ← vi.next (.int (intKindCore k))
      return (.int k (liftFlatInt k v), vi)
    | none => internal "lift_flat: integer primitive without kind"

/-- REF `lift_flat_list` with a fixed length (L1913-1917): `n` successive element lifts. -/
def liftFlatN (f : FlatCursor → P E σ (Val × FlatCursor)) :
    Nat → FlatCursor → P E σ (List Val × FlatCursor)
  | 0, vi => pure ([], vi)
  | n + 1, vi => do
    let (v, vi) ← f vi
    let (vs, vi) ← liftFlatN f n vi
    return (v :: vs, vi)

/-- The pointer and length of a variable-length list (REF `lift_flat_list`, L1918-1920) and
REF `load_list_from_range` on them, with element layout `l` and element loader `f`. -/
def liftFlatListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    (f : Nat → P E σ Val) (vi : FlatCursor) : P E σ (Val × FlatCursor) := do
  let (ptr, vi) ← vi.next (pointerType p)
  let (len, vi) ← vi.next (pointerType p)
  return (.list (← loadListFromRangeWith lim cx l f (flatNat ptr) (flatNat len)), vi)

/-- The `CoerceValueIter` of REF `lift_flat_variant` (L1934-1942) applied to the read payload
slots `xs` of joined types `haves`, where the case's own flattening wants `wants`: each slot
is `coerceLiftFlat have want x`; the slots past the case's own flattening are dropped (REF
reads and discards them). -/
def coerceLiftSlots : List CoreType → List CoreType → List FlatValue → List FlatValue
  | h :: hs, w :: ws, x :: xs => coerceLiftFlat h w x :: coerceLiftSlots hs ws xs
  | _, _, _ => []

/-- REF `lift_flat_variant(cx, vi, cases)` (L1928-1950) for `n` cases with joined payload
flat types `joined` (`flatten_variant` without the discriminant), case flat types `wants i`
and payload lifter `payload i` (run on a cursor over the coerced slots):
`case_index = vi.next('i32')`, `trap_if(case_index >= len(cases))` (`invalidDiscriminant`),
then the payload (see the module docstring for the read order). -/
def liftFlatVariantWith (n : Nat) (joined : List CoreType) (wants : Nat → List CoreType)
    (payload : Nat → FlatCursor → P E σ (Option Val × FlatCursor)) (vi : FlatCursor) :
    P E σ (Val × FlatCursor) := do
  let (d, vi) ← vi.next (.int .i32)
  let caseIndex := flatNat d
  trapIf (decide (caseIndex ≥ n)) .invalidDiscriminant
  let (xs, vi) ← vi.nextN joined
  let (v, _) ← payload caseIndex (.ofList (coerceLiftSlots joined (wants caseIndex) xs))
  return (.variant caseIndex v, vi)

/-- The case flat types of a despecialized `option t` (`[none, some t]`). -/
def optionWants (p : AddrType) (t : WIT.ClosedType RtId) : Nat → List CoreType
  | 1 => flatten p t
  | _ => []

/-- The case flat types of a despecialized `result ok err` (`[ok, err]`). -/
def resultWants (p : AddrType) (ok err : Option (WIT.ClosedType RtId)) : Nat → List CoreType
  | 0 => flattenOption p ok
  | 1 => flattenOption p err
  | _ => []

/-! ## Lifting -/

mutual
  /-- REF `lift_flat(cx, vi, t)` (L1869-1892) for pointer width `p`, by structural recursion
  on `t` (specialized types as their despecialization). -/
  def liftFlatAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      WIT.ClosedType RtId → FlatCursor → P E σ (Val × FlatCursor)
    | .prim prim, vi => liftFlatPrim lim q cx p prim vi
    | .ref r, _ => nomatch r
    | .list t, vi => liftFlatListWith lim cx p (layout p t) (loadAt lim q cx p t) vi
    | .fixedList t n, vi => do
      let (vs, vi) ← liftFlatN (liftFlatAt lim q cx p t) n vi
      return (.list vs, vi)
    | .record fields, vi => do
      let (vs, vi) ← liftFlatFields lim q cx p fields vi
      return (.record vs, vi)
    | .tuple ts, vi => do
      let (vs, vi) ← liftFlatTypes lim q cx p ts vi
      return (.record vs, vi)
    | .variant cases, vi =>
      liftFlatVariantWith cases.length (variantPayload (flattenCases p cases)) (caseFlat p cases)
        (liftFlatCaseAt lim q cx p cases) vi
    | .enum labels, vi =>
      liftFlatVariantWith labels.length [] (fun _ => []) (fun _ c => pure (none, c)) vi
    | .flags labels, vi => do
      let (v, vi) ← vi.next (.int .i32)
      return (.flags (unpackFlagsFromInt (flatNat v) labels), vi)
    | .option t, vi =>
      liftFlatVariantWith 2 (flatten p t) (optionWants p t)
        (fun i c => match i with
          | 1 => do
            let (v, c) ← liftFlatAt lim q cx p t c
            return (some v, c)
          | _ => pure (none, c))
        vi
    | .result ok err, vi =>
      liftFlatVariantWith 2 (joinFlat (flattenOption p ok) (flattenOption p err))
        (resultWants p ok err)
        (fun i c => match i with
          | 0 => liftFlatOpt lim q cx p ok c
          | 1 => liftFlatOpt lim q cx p err c
          | _ => pure (none, c))
        vi
    | .map k v, vi =>
      liftFlatListWith lim cx p (layout p (.record (mapEntryFields k v)))
        (loadMapEntryWith lim q cx p k (layout p v) (loadAt lim q cx p v)) vi
    | .own rt, vi => do
      let (i, vi) ← vi.next (.int .i32)
      return (.own (← liftOwn lim cx rt (flatNat i)), vi)
    | .borrow rt, vi => do
      let (i, vi) ← vi.next (.int .i32)
      return (.borrow (← liftBorrow lim cx rt (flatNat i)), vi)
    | .stream t, vi => do
      let (i, vi) ← vi.next (.int .i32)
      return (.stream (← liftStream lim cx t (flatNat i)), vi)
    | .future t, vi => do
      let (i, vi) ← vi.next (.int .i32)
      return (.future (← liftFuture lim cx t (flatNat i)), vi)
    | .errorContext, vi => do
      let (i, vi) ← vi.next (.int .i32)
      return (.errorContext (← liftErrorContext lim cx (flatNat i)), vi)
  termination_by structural t => t

  /-- REF `lift_flat_record(cx, vi, fields)` (L1922-1926): the fields in order. -/
  def liftFlatFields (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (String × WIT.ClosedType RtId) → FlatCursor → P E σ (List Val × FlatCursor)
    | [], vi => pure ([], vi)
    | (_, t) :: fields, vi => do
      let (v, vi) ← liftFlatAt lim q cx p t vi
      let (vs, vi) ← liftFlatFields lim q cx p fields vi
      return (v :: vs, vi)
  termination_by structural fields => fields

  /-- `liftFlatFields` for the fields of a despecialized tuple; also the direct path of REF
  `lift_flat_values` (`[lift_flat(cx, vi, t) for t in ts]`). -/
  def liftFlatTypes (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (WIT.ClosedType RtId) → FlatCursor → P E σ (List Val × FlatCursor)
    | [], vi => pure ([], vi)
    | t :: ts, vi => do
      let (v, vi) ← liftFlatAt lim q cx p t vi
      let (vs, vi) ← liftFlatTypes lim q cx p ts vi
      return (v :: vs, vi)
  termination_by structural ts => ts

  /-- The payload of case `i` of `cases` (REF `lift_flat_variant`'s `c = cases[case_index]`;
  `None` if `c.t is None`); `none` past the end (unreachable after the discriminant check). -/
  def liftFlatCaseAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (String × Option (WIT.ClosedType RtId)) → Nat → FlatCursor →
        P E σ (Option Val × FlatCursor)
    | [], _, vi => pure (none, vi)
    | (_, t) :: _, 0, vi => liftFlatOpt lim q cx p t vi
    | _ :: cases, i + 1, vi => liftFlatCaseAt lim q cx p cases i vi
  termination_by structural cases => cases

  /-- An optional payload: `None` for an absent type, `lift_flat(cx, vi, t)` otherwise. -/
  def liftFlatOpt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      Option (WIT.ClosedType RtId) → FlatCursor → P E σ (Option Val × FlatCursor)
    | none, vi => pure (none, vi)
    | some t, vi => do
      let (v, vi) ← liftFlatAt lim q cx p t vi
      return (some v, vi)
  termination_by structural t => t
end

/-- REF `lift_flat(cx, vi, t)` (L1869-1892). -/
def liftFlat (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (vi : FlatCursor)
    (t : WIT.ClosedType RtId) : P E σ (Val × FlatCursor) := do
  liftFlatAt lim q cx (← ptrType cx) t vi

/-- REF `lift_flat_values(cx, max_flat, vi, ts)` (L2040-2049). If
`len(flatten_types(ts)) > max_flat`, one pointer (of the pointer type) is read from `vi`,
`trap_if(ptr != align_to(ptr, alignment(tuple_type)))` (`unalignedPointer`),
`trap_if(ptr + elem_size(tuple_type) > len(memory))` (`outOfBounds`), and the tuple's fields
are loaded (`list(load(cx, ptr, tuple_type).values())`); otherwise each type is lifted from
`vi` in order. Returns the values and the advanced cursor. -/
def liftFlatValues (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (max : Nat)
    (vi : FlatCursor) (ts : List (WIT.ClosedType RtId)) : P E σ (List Val × FlatCursor) := do
  let p ← ptrType cx
  if (flattenTypes p ts).length > max then
    let (ptr, vi) ← vi.next (pointerType p)
    let l := layout p (.tuple ts : WIT.ClosedType RtId)
    trapIf (decide (flatNat ptr ≠ alignTo (flatNat ptr) l.alignment)) .unalignedPointer
    checkInBounds cx (flatNat ptr) l.size
    let vs ← loadTypesAt lim q cx p ts (flatNat ptr)
    return (vs, vi)
  else
    liftFlatTypes lim q cx p ts vi

/-! ## Lowering: non-recursive building blocks -/

/-- The scalar and string arms of REF `lower_flat` (L1963-1986) at primitive `pt`: `[int(v)]`
for `bool`, the integer itself (`lower_flat_signed`, L1988-1991, adds `2^32`/`2^64` to a
negative signed value: `lowerFlatInt`), `[maybe_scramble_nan32/64(v)]` (C7, `lowerFloat`),
`[char_to_i32(v)]`, and `lower_flat_string` (L1993-1995: `store_string_into_range`, then
`[ptr, packed_length]` of the pointer type). -/
def lowerFlatPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (pt : WIT.Primitive) (v : Val) : P E σ (List FlatValue) :=
  match pt, v with
  | .bool, .bool b => pure [i32Flat (if b then 1 else 0)]
  | .f32, .f32 x => do return [.float .f32 (← lowerFloat .f32 x)]
  | .f64, .f64 x => do return [.float .f64 (← lowerFloat .f64 x)]
  | .char, .char c => pure [.int .i32 (ABI.charToI32 c)]
  | .string, .string s => do
    let (ptr, len) ← storeStringIntoRange lim q cx s
    return [ptrFlat p ptr, ptrFlat p len]
  | pt, .int _ n =>
    match IntKind.ofPrimitive pt with
    | some k => pure [lowerFlatInt k n]
    | none => flatMismatch
  | _, _ => flatMismatch

/-- The `(have, want)` loop of REF `lower_flat_variant` (L2020-2029): for each pair of a
lowered payload value `v` of the case's own flat type `have` and the next joined slot type
`want` (popped from `flat_types`), `coerceLower have want v`. Returns the coerced payload and
the joined slot types not yet popped. The REF `IndexError` of popping an empty `flat_types`
(unreachable: the joined payload is at least as long as every case's) is `internal`. -/
def coerceLowerSlots : List CoreType → List CoreType → List FlatValue →
    P E σ (List FlatValue × List CoreType)
  | h :: hs, w :: ws, v :: vs => do
    let v' ← coerceLower h w v
    let (r, rest) ← coerceLowerSlots hs ws vs
    return (v' :: r, rest)
  | _ :: _, [], _ :: _ => internal "lower_flat_variant: payload wider than the joined slots"
  | _, ws, vs => pure (vs, ws)

/-- REF `lower_flat_variant(cx, v, cases)` (L2013-2032) for `n` cases with joined payload
flat types `joined`, the value's case index `i`, the case's own flat types `haves` and its
lowered payload `payload` (`[]` for a case without type): coerce the payload
(`coerceLowerSlots`), pad each remaining joined slot with `0` (`Value.zero` of the slot
type), and prepend the `i32` case index. An index `≥ n` is a shape mismatch (REF
`match_case` asserts, D-f). -/
def lowerFlatVariantWith (n : Nat) (joined : List CoreType) (i : Nat) (haves : List CoreType)
    (payload : P E σ (List FlatValue)) : P E σ (List FlatValue) :=
  if i < n then do
    let fl ← payload
    let (coerced, rest) ← coerceLowerSlots haves joined fl
    return i32Flat i :: (coerced ++ rest.map Execution.Runtime.Value.zero)
  else flatMismatch

/-! ## Lowering -/

mutual
  /-- REF `lower_flat(cx, v, t)` (L1963-1986) for pointer width `p`, by structural recursion
  on `t` (specialized types as their despecialization). -/
  def lowerFlatAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      Val → WIT.ClosedType RtId → P E σ (List FlatValue)
    | v, .prim pt => lowerFlatPrim lim q cx p pt v
    | _, .ref r => nomatch r
    | .list vs, .list u => do
      let (ptr, len) ← storeListIntoRange lim q cx vs u
      return [ptrFlat p ptr, ptrFlat p len]
    | .list vs, .fixedList u _ => do
      let parts ← Prog.mapM (fun e => lowerFlatAt lim q cx p e u) vs
      return parts.flatten
    | .list vs, .map k u => do
      let (ptr, len) ← storeListIntoRange lim q cx vs (.record (mapEntryFields k u))
      return [ptrFlat p ptr, ptrFlat p len]
    | .record vs, .record fields => lowerFlatFields lim q cx p vs fields
    | .record vs, .tuple ts => lowerFlatTypes lim q cx p vs ts
    | .variant i payload, .variant cases =>
      lowerFlatVariantWith cases.length (variantPayload (flattenCases p cases)) i
        (caseFlat p cases i) (lowerFlatCase lim q cx p i payload cases)
    | .variant i _, .enum labels => lowerFlatVariantWith labels.length [] i [] (pure [])
    | .variant i payload, .option u =>
      lowerFlatVariantWith 2 (flatten p u) i (optionWants p u i)
        (match i, payload with
          | 1, some x => lowerFlatAt lim q cx p x u
          | 1, none => flatMismatch
          | _, _ => pure [])
    | .variant i payload, .result ok err =>
      lowerFlatVariantWith 2 (joinFlat (flattenOption p ok) (flattenOption p err)) i
        (resultWants p ok err i)
        (match i with
          | 0 => lowerFlatOpt lim q cx p payload ok
          | 1 => lowerFlatOpt lim q cx p payload err
          | _ => pure [])
    | .flags bs, .flags labels => pure [i32Flat (packFlags (bs.take labels.length))]
    | .own rep, .own rt => do return [i32Flat (← lowerOwn lim cx rt rep)]
    | .borrow rep, .borrow rt => do return [i32Flat (← lowerBorrow lim cx rt rep)]
    | .stream e, .stream _ => do return [i32Flat (← lowerStream lim cx e)]
    | .future e, .future _ => do return [i32Flat (← lowerFuture lim cx e)]
    | .errorContext x, .errorContext => do return [i32Flat (← lowerErrorContext lim cx x)]
    | _, _ => flatMismatch
  termination_by structural _ t => t

  /-- REF `lower_flat_record(cx, v, fields)` (L2007-2011): the concatenated lowerings of the
  fields, in order (values positional; a length mismatch is a shape mismatch, D-f). -/
  def lowerFlatFields (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List Val → List (String × WIT.ClosedType RtId) → P E σ (List FlatValue)
    | [], [] => pure []
    | v :: vs, (_, t) :: fields => do
      let a ← lowerFlatAt lim q cx p v t
      let b ← lowerFlatFields lim q cx p vs fields
      return a ++ b
    | _, _ => flatMismatch
  termination_by structural _ fields => fields

  /-- `lowerFlatFields` for a despecialized tuple; also the direct path of REF
  `lower_flat_values` (`flat_vals += lower_flat(cx, vs[i], ts[i])`). -/
  def lowerFlatTypes (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List Val → List (WIT.ClosedType RtId) → P E σ (List FlatValue)
    | [], [] => pure []
    | v :: vs, t :: ts => do
      let a ← lowerFlatAt lim q cx p v t
      let b ← lowerFlatTypes lim q cx p vs ts
      return a ++ b
    | _, _ => flatMismatch
  termination_by structural _ ts => ts

  /-- The payload of case `i` (REF `lower_flat_variant`'s `c = cases[case_index]`: `[]` if
  `c.t is None`, else `lower_flat(cx, case_value, c.t)`). -/
  def lowerFlatCase (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
      (i : Nat) (payload : Option Val) :
      List (String × Option (WIT.ClosedType RtId)) → P E σ (List FlatValue)
    | [] => flatMismatch
    | (_, t) :: cases =>
      match i with
      | 0 => lowerFlatOpt lim q cx p payload t
      | i + 1 => lowerFlatCase lim q cx p i payload cases
  termination_by structural cases => cases

  /-- An optional payload: `[]` for an absent type, `lower_flat(cx, v, t)` otherwise (a
  missing value for a present type is a shape mismatch). -/
  def lowerFlatOpt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
      (payload : Option Val) : Option (WIT.ClosedType RtId) → P E σ (List FlatValue)
    | none => pure []
    | some t =>
      match payload with
      | some v => lowerFlatAt lim q cx p v t
      | none => flatMismatch
  termination_by structural t => t
end

/-- REF `lower_flat(cx, v, t)` (L1963-1986). -/
def lowerFlat (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (v : Val)
    (t : WIT.ClosedType RtId) : P E σ (List FlatValue) := do
  lowerFlatAt lim q cx (← ptrType cx) v t

/-- The spill pointer of REF `lower_flat_values` (L2055-2061) for a tuple of layout `l`:
`cx.allocate(alignment, elem_size)`, returned as the only flat value, when there is no
out-parameter; otherwise the next (pointer-typed) value of the out-parameter cursor, with no
flat value returned. -/
def spillPointer (cx : LiftLowerContext E) (p : AddrType) (l : Layout) :
    Option FlatCursor → P E σ (Nat × List FlatValue)
  | none => do
    let ptr ← allocate cx l.alignment.bytes l.size
    return (ptr, [ptrFlat p ptr])
  | some op => do
    let (v, _) ← op.next (pointerType p)
    return (flatNat v, [])

/-- REF `lower_flat_values(cx, max_flat, vs, ts, out_param)` (L2051-2070). If
`len(flatten_types(ts)) > max_flat`: the tuple's pointer is `spillPointer` (a fresh
allocation, or the out-parameter), then `trap_if` misaligned (`unalignedPointer`) and out of
bounds (`outOfBounds`) for `TupleType(ts)`, and `store` of the tuple value (`vs`
positionally); the result is `[ptr]` or `[]`. Otherwise the concatenated
`lower_flat(cx, vs[i], ts[i])`. -/
def lowerFlatValues (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (max : Nat)
    (vs : List Val) (ts : List (WIT.ClosedType RtId)) (outParam : Option FlatCursor) :
    P E σ (List FlatValue) := do
  let p ← ptrType cx
  if (flattenTypes p ts).length > max then
    let l := layout p (.tuple ts : WIT.ClosedType RtId)
    let (ptr, flatVals) ← spillPointer cx p l outParam
    trapIf (decide (ptr ≠ alignTo ptr l.alignment)) .unalignedPointer
    checkInBounds cx ptr l.size
    store lim q cx (.record vs) (.tuple ts) ptr
    return flatVals
  else
    lowerFlatTypes lim q cx p vs ts

/-! ## `unpack_callback_result` -/

/-- REF `unpack_callback_result(packed)` (L2153-2159): `code = packed & 0xf`,
`trap_if(code > CallbackCode.MAX)` (`unsupportedCallbackCode`),
`waitable_set_index = packed >> 4` (`Async.unpackCallbackResult`). -/
def unpackCallbackResult (packed : Nat) : P E σ (Async.CallbackCode × Nat) :=
  orTrap .unsupportedCallbackCode (Async.unpackCallbackResult packed)

/-! ## Unfolding equations of the entry points -/

section Equations

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)

end Equations

/-! ## Invariant preservation -/

namespace P.Inv

variable {I : CStore E → Prop}

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon
