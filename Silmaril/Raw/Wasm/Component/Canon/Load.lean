module

public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Scalar
public import Silmaril.Raw.Wasm.Component.Canon.Strings
public import Silmaril.Raw.Wasm.Component.Canon.Handles
public import Silmaril.Raw.Wasm.Component.ABI.Despecialize

/-!
# Type-directed load from memory

The Canonical ABI `load` family of REF `design/mvp/canonical-abi/definitions.py` at
component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>),
as specification programs in `P E σ` over closed types `WIT.ClosedType RtId`:

| Lean | REF (lines) |
| --- | --- |
| `load lim q cx t ptr` (via `loadAt`) | `load` (L1256-1281) |
| `loadInt` (reused, `Canon/Scalar.lean`) | `load_int` (L1283-1284) |
| `loadPrim` | primitive arms of `load`, `convert_int_to_bool`, `decode_i32/64_as_float` |
| `loadString` (reused, `Canon/Strings.lean`) | `load_string` (L1326-1329) |
| `loadList lim q cx ptr t len?` | `load_list` (L1376-1381) |
| `loadListFromRange lim q cx ptr n t` | `load_list_from_range` (L1383-1387) |
| `loadListFromValidRange lim q cx ptr n t` | `load_list_from_valid_range` (L1389-1393) |
| `loadRecord lim q cx ptr fields` (`loadFieldsAt`) | `load_record` (L1395-1401) |
| `loadVariant lim q cx ptr cases` (`loadVariantWith`, `loadCaseAt`) | `load_variant` (L1403-1412) |
| `loadFlags cx ptr labels` | `load_flags` (L1414-1416) |
| `unpackFlagsFromInt i labels` | `unpack_flags_from_int` (L1418-1423) |
| `liftOwn`, `liftBorrow` (reused, `Canon/Handles.lean`) | `lift_own`, `lift_borrow` |
| `liftErrorContext` (reused) | `lift_error_context` (L1368-1371) |
| `liftStream`, `liftFuture` (reused) | `lift_stream`, `lift_future` (L1441-1445) |

Sizes, alignments, field offsets and the variant payload offset are the layout
functions `ABI.layout p` (`Layout.size` = REF `elem_size`, `Layout.alignment` = REF
`alignment`), `ABI.alignTo`, `ABI.maxCaseAlignment` (REF `max_case_alignment`),
`ABI.discriminantAlignment` (REF `elem_size(discriminant_type(cases))`, D-b above `2^24`
cases) and `ABI.flagsAlignment` (REF `elem_size_flags`), with `p` the pointer width of
`cx`'s memory.

## Structure

`loadAt lim q cx p t ptr` is the recursive worker, defined by **structural** recursion over
the nested inductive `WIT.ValType` together with `loadFieldsAt` (record fields),
`loadTypesAt` (tuple fields), `loadCaseAt` (the payload of the selected variant case) and
`loadOptAt` (an optional payload), so it reduces in the kernel. The element loops of lists
and fixed lists are the non-recursive combinators `loadListFromValidRangeWith`/
`loadListFromRangeWith`/`loadListWith`, applied to the element loader `loadAt .. t`
(a structural recursive call under a lambda); `loadVariantWith` is the shared body of
`load_variant` for `variant`, `enum`, `option` and `result`. The REF-named entry points
(`load`, `loadList`, `loadListFromRange`, `loadListFromValidRange`, `loadRecord`,
`loadVariant`) read the pointer width once and call these. There is one `loadAt_*`
unfolding equation per constructor (`ref` is uninhabited); `load_list`, `load_fixedList`,
`load_record` and `load_variant` show that those arms are the REF helpers `load_list`,
`load_record` and `load_variant` through the entry points.

Specialized types are loaded as REF loads their despecialization (L1101-1108), without
rebuilding the despecialized type (which would not be structurally smaller): a `tuple` as a
record of its elements, an `enum` as a variant without payloads, `option t` as the variant
`[none, some t]`, `result ok err` as the variant `[ok, err]`, and `map k v` as a list of
2-field records `(k, v)` whose element layout is `layout p (.record (mapEntryFields k v))`;
the key (a primitive) is loaded with `loadPrim`. The `option`/`result` payload loaders match
on the case index (`0`, `1`, anything else `none`, unreachable after the discriminant check)
so that they agree with `loadCaseAt` on the despecialized case list at every index.
`loadAt_despecialize` proves `loadAt p (despecialize t) ptr = loadAt p t ptr` for every `t`.

## Deviations and non-claims

* D-f: REF `load` asserts `ptr == align_to(ptr, alignment(t))` and
  `ptr + elem_size(t) <= len(memory)`; these are the precondition `LoadPre`, not traps. The
  trapping entry points are `load_list_from_range` (trap `listTooLong` if
  `length * elem_size > lim.maxListBytes`, then `unalignedPointer`, then `outOfBounds`, in
  REF order) and `load_string_from_range` (`Canon/Strings.lean`). Without the precondition
  an out-of-bounds read traps `outOfBounds` through `readMem` (REF: a Python error).
* The pointer width `cx.opts.memory.ptr_type()` is read once per entry point (`ptrType cx`,
  a store read) and passed down as `p`, whereas REF recomputes it at every use. The memory's
  address type is immutable and no program here writes the core store, so this only removes
  redundant `get` operations.
* `loadInt` returns a Python-style `Int`; unsigned loads are non-negative and are converted
  with `Int.toNat` where a natural number (index, length, pointer) is needed.
* A variant whose discriminant is `≥ cases.length` traps `invalidDiscriminant`. Flags ignore
  every bit above the label count (REF `unpack_flags_from_int`). Fixed lists are loaded in
  place with no check (REF `load_list_from_valid_range` directly). Floats are canonicalized
  (`ABI.decodeFloat`); chars go through `convertI32ToChar` (trap `invalidChar`).
* Handles: `own`/`borrow` call `liftOwn`/`liftBorrow` with the resource type id (REF uses
  `t.rt`); `liftBorrow` requires `cx.scope` to be a subtask (REF assert, reaching `internal`
  otherwise). `stream`/`future` call `liftStream`/`liftFuture` with the element type.
* The quirk argument `q` is only passed on to `loadString` (no load-side quirk exists).
* Nothing is proved here about the loaded values (typing, round trips); those are in
  `Canon/Properties/LoadStoreBase.lean` and `Canon/Properties/LoadStore.lean`, and tests in
  `Tests/Values.lean` and `Tests/ValuesMemory.lean`. Proved: the unfolding equations, agreement with
  despecialization (`loadAt_despecialize`), and `P.Inv.load` (the load programs preserve every store
  invariant preserved by handle removal, `add_lender` and `lift_async_value`'s end release). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.ABI

variable {E : CoreEngine} {σ : Type}

/-! ## Precondition -/

/-! ## Non-recursive building blocks -/

/-! ## The recursive loader -/

/-! ## REF entry points -/

/-! ## Unfolding equations -/

section Equations

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) (ptr : Nat)

theorem loadAt_prim (prim : WIT.Primitive) :
    (loadAt lim q cx p (.prim prim) ptr : P E σ Val) = loadPrim lim q cx prim ptr := by
  rw [loadAt]

theorem loadAt_list (t : WIT.ClosedType RtId) :
    (loadAt lim q cx p (.list t) ptr : P E σ Val) =
      (do return .list (← loadListWith lim cx p (layout p t) (loadAt lim q cx p t) ptr)) := by
  rw [loadAt]

theorem loadAt_fixedList (t : WIT.ClosedType RtId) (n : Nat) :
    (loadAt lim q cx p (.fixedList t n) ptr : P E σ Val) =
      (do
        let vs ← loadListFromValidRangeWith (loadAt lim q cx p t) ptr n (layout p t).size
        return .list vs) := by
  rw [loadAt]

theorem loadAt_record (fields : List (String × WIT.ClosedType RtId)) :
    (loadAt lim q cx p (.record fields) ptr : P E σ Val) =
      (do return .record (← loadFieldsAt lim q cx p fields ptr)) := by
  rw [loadAt]

theorem loadAt_variant (cases : List (String × Option (WIT.ClosedType RtId))) :
    (loadAt lim q cx p (.variant cases) ptr : P E σ Val) =
      loadVariantWith cx cases.length (maxCaseAlignment (layoutCases p cases))
        (loadCaseAt lim q cx p cases) ptr := by
  rw [loadAt]

theorem loadAt_flags (labels : List String) :
    (loadAt lim q cx p (.flags labels) ptr : P E σ Val) = loadFlags cx ptr labels := by
  rw [loadAt]

theorem loadAt_tuple (ts : List (WIT.ClosedType RtId)) :
    (loadAt lim q cx p (.tuple ts) ptr : P E σ Val) =
      (do return .record (← loadTypesAt lim q cx p ts ptr)) := by
  rw [loadAt]

theorem loadAt_enum (labels : List String) :
    (loadAt lim q cx p (.enum labels) ptr : P E σ Val) =
      loadVariantWith cx labels.length (maxCaseAlignment (labels.map fun _ => none))
        (fun _ _ => pure none) ptr := by
  rw [loadAt]

theorem loadAt_map (k : WIT.KeyType) (v : WIT.ClosedType RtId) :
    (loadAt lim q cx p (.map k v) ptr : P E σ Val) =
      (do return .list (← loadListWith lim cx p (layout p (.record (mapEntryFields k v)))
        (loadMapEntryWith lim q cx p k (layout p v) (loadAt lim q cx p v)) ptr)) := by
  rw [loadAt]

theorem loadAt_own (rt : RtId) :
    (loadAt lim q cx p (.own rt) ptr : P E σ Val) =
      (do return .own (← liftOwn lim cx rt (← loadInt cx ptr 4).toNat)) := by
  rw [loadAt]

theorem loadAt_borrow (rt : RtId) :
    (loadAt lim q cx p (.borrow rt) ptr : P E σ Val) =
      (do return .borrow (← liftBorrow lim cx rt (← loadInt cx ptr 4).toNat)) := by
  rw [loadAt]

theorem loadAt_stream (t : Option (WIT.ClosedType RtId)) :
    (loadAt lim q cx p (.stream t) ptr : P E σ Val) =
      (do return .stream (← liftStream lim cx t (← loadInt cx ptr 4).toNat)) := by
  rw [loadAt]

theorem loadAt_future (t : Option (WIT.ClosedType RtId)) :
    (loadAt lim q cx p (.future t) ptr : P E σ Val) =
      (do return .future (← liftFuture lim cx t (← loadInt cx ptr 4).toNat)) := by
  rw [loadAt]

theorem loadAt_errorContext :
    (loadAt lim q cx p .errorContext ptr : P E σ Val) =
      (do return .errorContext (← liftErrorContext lim cx (← loadInt cx ptr 4).toNat)) := by
  rw [loadAt]

/-- A `list` arm of `loadAt` is REF `load_list(cx, ptr, t, None)`. -/
theorem load_list (t : WIT.ClosedType RtId) :
    (load lim q cx (.list t) ptr : P E σ Val) =
      (do return .list (← loadList lim q cx ptr t none)) := by
  simp only [load, loadList, loadAt_list, bind_assoc]

/-- A `fixed-list` arm is REF `load_list(cx, ptr, t, n)`. -/
theorem load_fixedList (t : WIT.ClosedType RtId) (n : Nat) :
    (load lim q cx (.fixedList t n) ptr : P E σ Val) =
      (do return .list (← loadList lim q cx ptr t (some n))) := by
  simp only [load, loadList, loadAt_fixedList, bind_assoc]

/-- A `record` arm is REF `load_record`. -/
theorem load_record (fields : List (String × WIT.ClosedType RtId)) :
    (load lim q cx (.record fields) ptr : P E σ Val) = loadRecord lim q cx ptr fields := by
  simp only [load, loadRecord, loadAt_record]

/-- A `variant` arm is REF `load_variant`. -/
theorem load_variant (cases : List (String × Option (WIT.ClosedType RtId))) :
    (load lim q cx (.variant cases) ptr : P E σ Val) = loadVariant lim q cx ptr cases := by
  simp only [load, loadVariant, loadAt_variant]

/-- `load_list(.., None)` is `load_list_from_range` on the loaded `(begin, length)` pair. -/
theorem loadList_none (t : WIT.ClosedType RtId) :
    (loadList lim q cx ptr t none : P E σ (List Val)) = (do
      let p ← ptrType cx
      let begin ← loadPtrWord cx p ptr
      let length ← loadPtrWord cx p (ptr + ptrSizeOf p)
      loadListFromRangeWith lim cx (layout p t) (loadAt lim q cx p t) begin length) := rfl

end Equations

/-! ## Agreement with despecialization -/

section Despecialize

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)

/-- The fields of a despecialized tuple load as the tuple's elements. -/
theorem loadFieldsAt_tupleFieldsFrom (ts : List (WIT.ClosedType RtId)) (i ptr : Nat) :
    (loadFieldsAt lim q cx p (tupleFieldsFrom i ts) ptr : P E σ (List Val)) =
      loadTypesAt lim q cx p ts ptr := by
  induction ts generalizing i ptr with
  | nil => rw [tupleFieldsFrom, loadFieldsAt, loadTypesAt]
  | cons t ts ih => rw [tupleFieldsFrom, loadFieldsAt, loadTypesAt]; simp only [ih]

/-- Every case of a despecialized `enum` has no payload. -/
theorem loadCaseAt_enum (labels : List String) (i ptr : Nat) :
    (loadCaseAt lim q cx p (labels.map fun l => (l, none)) i ptr : P E σ (Option Val)) =
      pure none := by
  induction labels generalizing i with
  | nil => rw [List.map_nil, loadCaseAt]
  | cons l ls ih =>
    cases i with
    | zero => rw [List.map_cons, loadCaseAt, loadOptAt]
    | succ i => rw [List.map_cons, loadCaseAt, ih]

theorem maxCaseAlignment_map_none {α : Type} (xs : List α) :
    maxCaseAlignment (xs.map fun _ => none) = .one := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp only [List.map_cons, maxCaseAlignment, ih]

/-- The element of a despecialized `map k v`, the record `{"0": k, "1": v}`, loads as
`loadMapEntryWith`. -/
theorem loadAt_mapEntry (k : WIT.KeyType) (v : WIT.ClosedType RtId) (ptr : Nat) :
    (loadAt lim q cx p (.record (mapEntryFields k v)) ptr : P E σ Val) =
      loadMapEntryWith lim q cx p k (layout p v) (loadAt lim q cx p v) ptr := by
  rw [loadAt, mapEntryFields]
  simp only [loadFieldsAt]
  rw [loadAt_prim, loadMapEntryWith]
  simp only [bind_assoc, pure_bind]

/-- Loading a specialized type is loading its REF despecialization (L1101-1108): the
hand-inlined `tuple`/`enum`/`option`/`result`/`map` arms of `loadAt` agree with the
`record`/`variant`/`list` arms on `despecialize t`; every other type is unchanged. -/
theorem loadAt_despecialize (t : WIT.ClosedType RtId) (ptr : Nat) :
    (loadAt lim q cx p (despecialize t) ptr : P E σ Val) = loadAt lim q cx p t ptr := by
  cases t with
  | tuple ts => rw [despecialize, loadAt, loadAt, loadFieldsAt_tupleFieldsFrom]
  | enum labels =>
    have hc : (loadCaseAt lim q cx p (labels.map fun l => (l, none)) : _ → _ → P E σ _) =
        fun _ _ => pure none := funext fun i => funext fun ptr => loadCaseAt_enum ..
    rw [despecialize, loadAt, loadAt, hc, layoutCases_enum, List.length_map,
      maxCaseAlignment_replicate_none, maxCaseAlignment_map_none]
  | option t =>
    rw [despecialize, loadAt, loadAt, layoutCases, layoutCases, layoutCases, layoutOption,
      layoutOption]
    congr 1
    funext i ptr'
    rcases i with _ | _ | i <;> simp only [loadCaseAt, loadOptAt]
  | result ok err =>
    rw [despecialize, loadAt, loadAt, layoutCases, layoutCases, layoutCases]
    congr 1
    funext i ptr'
    rcases i with _ | _ | i <;> simp only [loadCaseAt]
  | map k v =>
    have hm : (loadAt lim q cx p (.record (mapEntryFields k v)) : _ → P E σ Val) =
        loadMapEntryWith lim q cx p k (layout p v) (loadAt lim q cx p v) :=
      funext (loadAt_mapEntry lim q cx p k v)
    rw [despecialize, loadAt, loadAt, hm]
  | _ => rfl

end Despecialize

/-! ## Invariant preservation -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem load (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (t : WIT.ClosedType RtId) (ptr : Nat) : P.Inv I (Canon.load lim q cx t ptr : P E σ Val) :=
  bind (ptrType cx) fun p => loadAt h lim q cx p t ptr

theorem loadListFromRange (h : LoadPres I) (lim : Limits) (q : Quirks)
    (cx : LiftLowerContext E) (ptr length : Nat) (t : WIT.ClosedType RtId) :
    P.Inv I (Canon.loadListFromRange lim q cx ptr length t : P E σ (List Val)) :=
  bind (ptrType cx) fun p => loadListFromRangeWith lim cx _ (loadAt h lim q cx p t) _ _

theorem loadList (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) (t : WIT.ClosedType RtId) (n : Option Nat) :
    P.Inv I (Canon.loadList lim q cx ptr t n : P E σ (List Val)) :=
  bind (ptrType cx) fun p => by
    cases n with
    | some n => exact loadListFromValidRangeWith (loadAt h lim q cx p t) _ _ _
    | none => exact loadListWith lim cx p _ (loadAt h lim q cx p t) _

theorem loadRecord (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) (fields : List (String × WIT.ClosedType RtId)) :
    P.Inv I (Canon.loadRecord lim q cx ptr fields : P E σ Val) :=
  bind (ptrType cx) fun p => bind (loadFieldsAt h lim q cx p fields ptr) fun _ => pure _

theorem loadVariant (h : LoadPres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr : Nat) (cases : List (String × Option (WIT.ClosedType RtId))) :
    P.Inv I (Canon.loadVariant lim q cx ptr cases : P E σ Val) :=
  bind (ptrType cx) fun p => loadVariantWith _ _ _ (loadCaseAt h lim q cx p cases) _

end P.Inv

/-! ## Examples -/

section Examples

/-- `unpack_flags_from_int(0b1100101, [a, b, c, d])`: bits above the label count are
ignored. -/
example : unpackFlagsFromInt 0b1100101 ["a", "b", "c", "d"] = [true, false, true, false] := by
  decide

/-- Loading a `list<u8>` from its `(ptr, len)` slot is `load_list(.., None)`. -/
example (cx : LiftLowerContext E) (ptr : Nat) : P E σ Val :=
  load Limits.spec Quirks.none cx (.list (.prim .u8)) ptr

/-- A 2-case variant (e.g. `option`/`result`) has a 1-byte discriminant. -/
example : (discriminantAlignment 2).bytes = 1 := rfl

/-- The structural definition unfolds by `rfl`: `option<u8>` is the 2-case variant whose
payload is loaded by `loadPrim` (layouts are left symbolic: `ABI.layout` is well-founded and
is evaluated with `decide +kernel`, as below). -/
example (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat) :
    (loadAt lim q cx .i32 (.option (.prim .u8)) ptr : P E σ Val) =
      loadVariantWith cx 2
        (maxCaseAlignment [none, some (layout (Resource := RtId) .i32 (.prim .u8))])
        (fun i ptr' => match i with
          | 0 => pure none
          | 1 => do return some (← loadPrim lim q cx .u8 ptr')
          | _ + 2 => pure none) ptr := rfl

/-- The payload of `option<u8>` is at offset 1 (1-byte discriminant, alignment 1). -/
example : maxCaseAlignment [none, some (layout (Resource := RtId) .i32 (.prim .u8))] = .one := by
  decide +kernel

end Examples

end Silmaril.Wasm.Component.Canon
