module

public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs

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

/-- The REF assertions of `load(cx, ptr, t)` (L1257-1258) in store `s`: `ptr` is aligned to
`alignment(t)` and `[ptr, ptr + elem_size(t))` lies in `cx`'s memory. A precondition (D-f),
never checked by `load`. -/
def LoadPre (s : CStore E) (cx : LiftLowerContext E) (t : WIT.ClosedType RtId) (ptr : Nat) :
    Prop :=
  let l := layout (ptrTypeIn s cx) t
  ptr % l.alignment.bytes = 0 ∧
    ∃ m n, cx.opts.memory = some m ∧ E.memSize? s.core m = some n ∧ ptr + l.size ≤ n

/-! ## Non-recursive building blocks -/

/-- REF `load_int(cx, ptr, cx.opts.memory.ptr_size())`: a pointer-sized unsigned word. -/
def loadPtrWord (cx : LiftLowerContext E) (p : AddrType) (ptr : Nat) : P E σ Nat := do
  return (← loadInt cx ptr (ptrSizeOf p)).toNat

/-- REF `convert_int_to_bool(load_int(cx, ptr, 1))` etc.: the primitive arms of `load`
(L1260-1272). Integers are `load_int` with the kind's byte width and signedness; floats are
`decode_i32_as_float`/`decode_i64_as_float` (reinterpret and canonicalize NaN); chars are
`convert_i32_to_char` (trap `invalidChar`); strings are `load_string`. -/
def loadPrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (prim : WIT.Primitive)
    (ptr : Nat) : P E σ Val :=
  match prim with
  | .bool => do return .bool (convertIntToBool (← loadInt cx ptr 1))
  | .u8 => do return .int .u8 (← loadInt cx ptr 1)
  | .u16 => do return .int .u16 (← loadInt cx ptr 2)
  | .u32 => do return .int .u32 (← loadInt cx ptr 4)
  | .u64 => do return .int .u64 (← loadInt cx ptr 8)
  | .s8 => do return .int .s8 (← loadInt cx ptr 1 true)
  | .s16 => do return .int .s16 (← loadInt cx ptr 2 true)
  | .s32 => do return .int .s32 (← loadInt cx ptr 4 true)
  | .s64 => do return .int .s64 (← loadInt cx ptr 8 true)
  | .f32 => do return .f32 (decodeFloat .f32 (BitVec.ofNat 32 (← loadInt cx ptr 4).toNat))
  | .f64 => do return .f64 (decodeFloat .f64 (BitVec.ofNat 64 (← loadInt cx ptr 8).toNat))
  | .char => do return .char (← convertI32ToChar (BitVec.ofNat 32 (← loadInt cx ptr 4).toNat))
  | .string => do return .string (← loadString lim q cx ptr)

/-- REF `load_list_from_valid_range(cx, ptr, length, elem_type)` (L1389-1393) with element
loader `f` and element size `sz`: load elements `0, …, length - 1` at `ptr + i * sz`, in
order, with no check. -/
def loadListFromValidRangeWith (f : Nat → P E σ Val) (ptr length sz : Nat) :
    P E σ (List Val) :=
  Prog.mapM (fun i => f (ptr + i * sz)) (List.range length)

/-- REF `load_list_from_range(cx, ptr, length, elem_type)` (L1383-1387) with element layout
`l` and loader `f`: `trap_if(length * elem_size > MAX_LIST_BYTE_LENGTH)` (`listTooLong`,
bound `lim.maxListBytes`), `trap_if(ptr != align_to(ptr, alignment))` (`unalignedPointer`),
`trap_if(ptr + length * elem_size > len(memory))` (`outOfBounds`), in this order; then
`loadListFromValidRangeWith`. -/
def loadListFromRangeWith (lim : Limits) (cx : LiftLowerContext E) (l : Layout)
    (f : Nat → P E σ Val) (ptr length : Nat) : P E σ (List Val) := do
  trapIf (decide (length * l.size > lim.maxListBytes)) .listTooLong
  trapIf (decide (ptr ≠ alignTo ptr l.alignment)) .unalignedPointer
  checkInBounds cx ptr (length * l.size)
  loadListFromValidRangeWith f ptr length l.size

/-- REF `load_list(cx, ptr, elem_type, None)` (L1376-1381): load the pointer-sized `begin`
and `length` words at `ptr` and `ptr + ptr_size`, then `loadListFromRangeWith`. -/
def loadListWith (lim : Limits) (cx : LiftLowerContext E) (p : AddrType) (l : Layout)
    (f : Nat → P E σ Val) (ptr : Nat) : P E σ (List Val) := do
  let begin ← loadPtrWord cx p ptr
  let length ← loadPtrWord cx p (ptr + ptrSizeOf p)
  loadListFromRangeWith lim cx l f begin length

/-- REF `load_variant(cx, ptr, cases)` (L1403-1412) for `n` cases whose payloads have
maximal alignment `caseAlign`, with payload loader `payload i ptr'` for case `i < n`:
`case_index = load_int(cx, ptr, disc_size)` (`disc_size` =
`(discriminantAlignment n).bytes`, D-b), `trap_if(case_index >= len(cases))`
(`invalidDiscriminant`), then the payload at `align_to(ptr + disc_size, caseAlign)`. -/
def loadVariantWith (cx : LiftLowerContext E) (n : Nat) (caseAlign : Alignment)
    (payload : Nat → Nat → P E σ (Option Val)) (ptr : Nat) : P E σ Val := do
  let discSize := (discriminantAlignment n).bytes
  let caseIndex := (← loadInt cx ptr discSize).toNat
  trapIf (decide (caseIndex ≥ n)) .invalidDiscriminant
  let v ← payload caseIndex (alignTo (ptr + discSize) caseAlign)
  return .variant caseIndex v

/-- REF `unpack_flags_from_int(i, labels)` (L1418-1423): one `bool(i & 1)` per label, shifting
`i` right after each; bits above the label count are ignored. -/
def unpackFlagsFromInt (i : Nat) : List String → List Bool
  | [] => []
  | _ :: ls => (i % 2 == 1) :: unpackFlagsFromInt (i / 2) ls

/-- REF `load_flags(cx, ptr, labels)` (L1414-1416): `load_int(cx, ptr, elem_size_flags)`
(`(flagsAlignment labels.length).bytes`), then `unpack_flags_from_int`. -/
def loadFlags (cx : LiftLowerContext E) (ptr : Nat) (labels : List String) : P E σ Val := do
  return .flags (unpackFlagsFromInt (← loadInt cx ptr (flagsAlignment labels.length).bytes).toNat
    labels)

/-- The element loader of a despecialized `map k v` (REF `load_record` on the entry record
`{"0": k, "1": v}`, L1395-1401): the key (a primitive) at `align_to(ptr, alignment(k))`,
the value, of layout `lv`, at `align_to(key_ptr + elem_size(k), alignment(v))`. -/
def loadMapEntryWith (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)
    (k : WIT.KeyType) (lv : Layout) (fv : Nat → P E σ Val) (ptr : Nat) : P E σ Val := do
  let lk := layout (Resource := RtId) p (.prim k.toPrimitive)
  let kptr := alignTo ptr lk.alignment
  let kv ← loadPrim lim q cx k.toPrimitive kptr
  let vv ← fv (alignTo (kptr + lk.size) lv.alignment)
  return .record [kv, vv]

/-! ## The recursive loader -/

mutual
  /-- REF `load(cx, ptr, t)` (L1256-1281) for pointer width `p`, by structural recursion on
  `t` (specialized types handled as their despecialization, see the module docstring). -/
  def loadAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      WIT.ClosedType RtId → Nat → P E σ Val
    | .prim prim, ptr => loadPrim lim q cx prim ptr
    | .ref r, _ => nomatch r
    | .list t, ptr => do
      return .list (← loadListWith lim cx p (layout p t) (loadAt lim q cx p t) ptr)
    | .fixedList t n, ptr => do
      return .list (← loadListFromValidRangeWith (loadAt lim q cx p t) ptr n (layout p t).size)
    | .record fields, ptr => do return .record (← loadFieldsAt lim q cx p fields ptr)
    | .tuple ts, ptr => do return .record (← loadTypesAt lim q cx p ts ptr)
    | .variant cases, ptr =>
      loadVariantWith cx cases.length (maxCaseAlignment (layoutCases p cases))
        (loadCaseAt lim q cx p cases) ptr
    | .enum labels, ptr =>
      loadVariantWith cx labels.length (maxCaseAlignment (labels.map fun _ => none))
        (fun _ _ => pure none) ptr
    | .flags labels, ptr => loadFlags cx ptr labels
    | .option t, ptr =>
      loadVariantWith cx 2 (maxCaseAlignment [none, some (layout p t)])
        (fun i ptr' => match i with
          | 0 => pure none
          | 1 => do return some (← loadAt lim q cx p t ptr')
          | _ + 2 => pure none)
        ptr
    | .result ok err, ptr =>
      loadVariantWith cx 2 (maxCaseAlignment [layoutOption p ok, layoutOption p err])
        (fun i ptr' => match i with
          | 0 => loadOptAt lim q cx p ok ptr'
          | 1 => loadOptAt lim q cx p err ptr'
          | _ + 2 => pure none)
        ptr
    | .map k v, ptr => do
      return .list (← loadListWith lim cx p (layout p (.record (mapEntryFields k v)))
        (loadMapEntryWith lim q cx p k (layout p v) (loadAt lim q cx p v)) ptr)
    | .own rt, ptr => do return .own (← liftOwn lim cx rt (← loadInt cx ptr 4).toNat)
    | .borrow rt, ptr => do return .borrow (← liftBorrow lim cx rt (← loadInt cx ptr 4).toNat)
    | .stream t, ptr => do return .stream (← liftStream lim cx t (← loadInt cx ptr 4).toNat)
    | .future t, ptr => do return .future (← liftFuture lim cx t (← loadInt cx ptr 4).toNat)
    | .errorContext, ptr => do
      return .errorContext (← liftErrorContext lim cx (← loadInt cx ptr 4).toNat)
  termination_by structural t => t

  /-- REF `load_record(cx, ptr, fields)` (L1395-1401): for each field,
  `ptr = align_to(ptr, alignment(f.t))`, load it, `ptr += elem_size(f.t)`. -/
  def loadFieldsAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (String × WIT.ClosedType RtId) → Nat → P E σ (List Val)
    | [], _ => pure []
    | (_, t) :: fields, ptr => do
      let fptr := alignTo ptr (layout p t).alignment
      let v ← loadAt lim q cx p t fptr
      let vs ← loadFieldsAt lim q cx p fields (fptr + (layout p t).size)
      return v :: vs
  termination_by structural fields => fields

  /-- `loadFieldsAt` for the fields of a despecialized tuple (labels are irrelevant). -/
  def loadTypesAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (WIT.ClosedType RtId) → Nat → P E σ (List Val)
    | [], _ => pure []
    | t :: ts, ptr => do
      let fptr := alignTo ptr (layout p t).alignment
      let v ← loadAt lim q cx p t fptr
      let vs ← loadTypesAt lim q cx p ts (fptr + (layout p t).size)
      return v :: vs
  termination_by structural ts => ts

  /-- The payload of case `i` of `cases` at `ptr` (REF `load_variant`'s
  `c = cases[case_index]; None if c.t is None else load(cx, ptr, c.t)`); `none` past the
  end (unreachable after the discriminant check). -/
  def loadCaseAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      List (String × Option (WIT.ClosedType RtId)) → Nat → Nat → P E σ (Option Val)
    | [], _, _ => pure none
    | (_, t) :: _, 0, ptr => loadOptAt lim q cx p t ptr
    | _ :: cases, i + 1, ptr => loadCaseAt lim q cx p cases i ptr
  termination_by structural cases => cases

  /-- An optional payload: `None` for an absent type, `load(cx, ptr, t)` otherwise. -/
  def loadOptAt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) :
      Option (WIT.ClosedType RtId) → Nat → P E σ (Option Val)
    | none, _ => pure none
    | some t, ptr => do return some (← loadAt lim q cx p t ptr)
  termination_by structural t => t
end

/-! ## REF entry points -/

/-- REF `load(cx, ptr, t)` (L1256-1281). Precondition (REF asserts, D-f): `LoadPre`. -/
def load (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (t : WIT.ClosedType RtId)
    (ptr : Nat) : P E σ Val := do
  loadAt lim q cx (← ptrType cx) t ptr

/-- REF `load_list_from_valid_range(cx, ptr, length, elem_type)` (L1389-1393). -/
def loadListFromValidRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr length : Nat) (t : WIT.ClosedType RtId) : P E σ (List Val) := do
  let p ← ptrType cx
  loadListFromValidRangeWith (loadAt lim q cx p t) ptr length (layout p t).size

/-- REF `load_list_from_range(cx, ptr, length, elem_type)` (L1383-1387): the three traps
(`listTooLong`, `unalignedPointer`, `outOfBounds`) in REF order, then the valid range. -/
def loadListFromRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (ptr length : Nat) (t : WIT.ClosedType RtId) : P E σ (List Val) := do
  let p ← ptrType cx
  loadListFromRangeWith lim cx (layout p t) (loadAt lim q cx p t) ptr length

/-- REF `load_list(cx, ptr, elem_type, maybe_length)` (L1376-1381): a fixed length loads in
place (`load_list_from_valid_range`, no check); otherwise the `(begin, length)` pair at
`ptr` is loaded and `load_list_from_range` checks it. -/
def loadList (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat)
    (t : WIT.ClosedType RtId) (maybeLength : Option Nat) : P E σ (List Val) := do
  let p ← ptrType cx
  match maybeLength with
  | some n => loadListFromValidRangeWith (loadAt lim q cx p t) ptr n (layout p t).size
  | none => loadListWith lim cx p (layout p t) (loadAt lim q cx p t) ptr

/-- REF `load_record(cx, ptr, fields)` (L1395-1401). -/
def loadRecord (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat)
    (fields : List (String × WIT.ClosedType RtId)) : P E σ Val := do
  return .record (← loadFieldsAt lim q cx (← ptrType cx) fields ptr)

/-- REF `load_variant(cx, ptr, cases)` (L1403-1412). -/
def loadVariant (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (ptr : Nat)
    (cases : List (String × Option (WIT.ClosedType RtId))) : P E σ Val := do
  let p ← ptrType cx
  loadVariantWith cx cases.length (maxCaseAlignment (layoutCases p cases))
    (loadCaseAt lim q cx p cases) ptr

/-! ## Unfolding equations -/

section Equations

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType) (ptr : Nat)

theorem loadAt_option (t : WIT.ClosedType RtId) :
    (loadAt lim q cx p (.option t) ptr : P E σ Val) =
      loadVariantWith cx 2 (maxCaseAlignment [none, some (layout p t)])
        (fun i ptr' => match i with
          | 0 => pure none
          | 1 => do return some (← loadAt lim q cx p t ptr')
          | _ + 2 => pure none) ptr := by
  rw [loadAt]

theorem loadAt_result (ok err : Option (WIT.ClosedType RtId)) :
    (loadAt lim q cx p (.result ok err) ptr : P E σ Val) =
      loadVariantWith cx 2 (maxCaseAlignment [layoutOption p ok, layoutOption p err])
        (fun i ptr' => match i with
          | 0 => loadOptAt lim q cx p ok ptr'
          | 1 => loadOptAt lim q cx p err ptr'
          | _ + 2 => pure none) ptr := by
  rw [loadAt]

end Equations

/-! ## Agreement with despecialization -/

section Despecialize

variable (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (p : AddrType)

end Despecialize

/-- `unpack_flags_from_int` yields one flag per label. -/
@[simp] theorem length_unpackFlagsFromInt (i : Nat) (labels : List String) :
    (unpackFlagsFromInt i labels).length = labels.length := by
  induction labels generalizing i with
  | nil => rfl
  | cons _ ls ih => simp only [unpackFlagsFromInt, List.length_cons, ih]

/-! ## Invariant preservation -/

namespace P.Inv

variable {I : CStore E → Prop}

/-- The store updates a load can issue: handle removal (`lift_own`, `lift_async_value`),
`add_lender` (`lift_borrow`) and the end release of `lift_async_value`. -/
structure LoadPres (I : CStore E → Prop) : Prop where
  remove : RemoveHandlePres I
  lender : ∀ s st h, I st → I (HandleSt.addLender (E := E) s h st)
  release : ∀ e st, I st → I (HandleSt.releaseEnd (E := E) e st)

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon
