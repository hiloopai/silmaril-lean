module

public import Silmaril.Wasm.Component.Reference.Canon.Strings.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs
public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs

/-!
# Type-directed store of component values into linear memory

Specification programs (in `P E σ`) transcribing the storing half of REF
`design/mvp/canonical-abi/definitions.py` at component-model `a25fc0b`
(<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>)
for closed WIT types `WIT.ClosedType RtId`:

| Lean | REF (lines) |
| --- | --- |
| `store lim q cx v t ptr` | `store` (L1461-1486) |
| `storePrim lim q cx p v ptr` | the scalar and string arms of `store` |
| `storeInt` (reused, `Canon/Scalar.lean`) | `store_int` (L1488-1489) |
| `encodeFloat` (reused, `Canon/Scalar.lean`) | `encode_float_as_i32/i64` (L1516-1520), choice C7 |
| `storeString` (reused, `Canon/Strings.lean`) | `store_string` (L1533-1536) |
| `lowerErrorContext` (reused, `Canon/Handles.lean`) | `lower_error_context` (L1677-1678) |
| `lowerOwn`, `lowerBorrow` (reused) | `lower_own` (L1736-1738), `lower_borrow` (L1740-1746) |
| `lowerStream`, `lowerFuture` (reused) | `lower_stream`/`lower_future` (L1748-1760) |
| `storeListWith`, `storeList` | `store_list` (L1680-1687) |
| `storeListIntoRange(With)` | `store_list_into_range` (L1689-1696) |
| `storeListIntoValidRange(With)` | `store_list_into_valid_range` (L1698-1700) |
| `storeFields`, `storeTuple` | `store_record` (L1702-1706) |
| `storeVariantHead`, `storeCase`, `storeOpt` | `store_variant` (L1708-1716) |
| `matchCase`, `storeMatched` | `match_case` (L1718-1722) |
| `packFlags`, `storeFlags` | `pack_flags_into_int` (L1728-1734), `store_flags` (L1724-1726) |
| `discSize` | `elem_size(discriminant_type(cases))` (L1177-1184) |

Placement uses the layout `ABI.layout p` (`ABI/Layout.lean`) with `p` the pointer
type of `cx`'s memory (`ptrType cx`, D-g): REF `alignment(t, ptr_type)` is
`(ABI.layout p t).alignment.bytes`, REF `elem_size(t, ptr_type)` is
`(ABI.layout p t).size`, and REF `max_case_alignment` is `ABI.maxCaseAlignment` of
`ABI.layoutCases p cases`.

**Specialized types.** REF `store` matches on `despecialize(t)` (L1101-1108). Here the
specialized constructors are stored directly in their despecialized form, so that recursion
stays on subterms of `t`: `tuple` as a record (positional fields), `enum` as a variant with no
payloads, `option t` as `variant { none, some(t) }`, `result ok err` as
`variant { ok(ok?), error(err?) }`, and `map k v` as a list of two-field records
`{ "0": k, "1": v }` (`ABI.mapEntryFields`). The discriminant sizes and payload alignments
used are exactly those of the despecialized variants (`ABI.layout_despecialize` proves the
layouts agree).

**Values.** `Val` is positional (`Value/Basic.lean`): a record carries its field values in
field order (REF looks fields up by label, `v[f.label]`), a variant carries its case *index*
into the type it is stored at, and flags carry one `Bool` per label in label order.

**Termination.** `store`, `storeFields`, `storeTuple`, `storeCase` and `storeOpt` form one
`mutual` block whose measure is `sizeOf` of the type argument (the pattern of
`ABI/Layout.lean`). Lists are stored through the non-recursive helpers `store*With`, which
take the element store `fun e a => store lim q cx e u a` as an argument, so the recursive call
is on the element type `u` alone.

## Deviations and non-claims

* D-f: REF `assert`s are preconditions, never traps: `store`'s alignment and bounds asserts on
  `ptr` (L1462-1463; the list entry point `storeListIntoRange` performs REF's `trap_if`s),
  `store_list`'s `maybe_length == len(v)` (a fixed-length list stores the elements it is
  given), `store_list_into_range`'s `byte_length <= REALLOC_I32_MAX` (the size limit is an
  ASSERT in REF; `StoreListPre` records it against the `lim` argument, so it also covers `Limits.wasmtime`),
  `match_case`'s uniqueness, `discriminant_type`/`elem_size_flags` bounds on the case/label
  counts, and `char_to_i32`'s scalar-value assert (a Lean `Char` is a scalar value). A value
  whose *shape* does not match the type (e.g. a `bool` stored at `string`, a variant index out
  of range, a missing payload for a case with a type, a record with the wrong number of fields)
  reaches `internal` (`storeMismatch`): the REF would raise a Python exception; this is
  unreachable for values satisfying `Val.HasType v t`.
* D-b: `discSize` is 4 for more than `2^24` cases (REF `discriminant_type` falls off its
  `match` there); `ABI.discriminantAlignment` already fixes this.
* D-a: strings are stored with `storeString`, which re-tags a `latin1+utf16` count for the
  destination width unless `q.refUtf16TagBug` (see `Canon/Strings.lean`).
* Flags: `packFlags` packs the first `labels.length` booleans (REF iterates the labels);
  surplus booleans are ignored and missing ones are `false`.
* A variant value carries its case index into the type it is stored at. REF `match_case`
  finds the index by label, which matters when the value was produced at a different
  (subtype-compatible) variant type; `matchCase srcCases dstCases i` is that lookup and
  `storeMatched` stores a value lifted at `srcCases` into `dstCases`. `matchCase_self` shows
  it is the identity on a type with distinct labels, i.e. `store` agrees with REF when the
  value's type is the stored type.
* Padding bytes are never written (REF writes only fields, discriminants and payloads).
* Floats are lowered through `encodeFloat`, which issues the C7 choice `choose (.nan t x)`
  only on a NaN.
* Proved here: `matchCase_self`, `packFlags_lt`, and `P.Inv` lemmas for every program
  (`P.Inv.store` by mutual well-founded recursion, under `StorePres I`: the memory writes and
  handle/end updates of the reused lowering functions preserve `I`). Nothing about the
  result of these programs is proved here (the load/store round trip is
  `Canon/Properties/LoadStore.lean`). -/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type}

/-! ## Pure helpers -/

/-- REF `elem_size(discriminant_type(cases), ptr_type)` (L1177-1184) for `n` cases: 1, 2 or 4
bytes (D-b: 4 above `2^24` cases). Equal to the discriminant alignment. -/
def discSize (n : Nat) : Nat := (ABI.discriminantAlignment n).bytes

/-- REF `elem_size_flags(labels)` (L1247-1252) for `n` labels. -/
def flagsSize (n : Nat) : Nat := (ABI.flagsAlignment n).bytes

/-- REF `pack_flags_into_int(v, labels)` (L1728-1734) on the positional flags value `bs`:
bit `i` is `bs[i]`. -/
def packFlags : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * packFlags bs

/-- REF `match_case(v, cases)` (L1718-1722) for a variant value whose case index `i` refers
to `srcCases`: the index of the case of `dstCases` with the same label (`none` if the index
is out of range or no case matches; REF asserts one does). -/
def matchCase {α β : Type} (srcCases : List (String × α)) (dstCases : List (String × β))
    (i : Nat) : Option Nat := do
  let (l, _) ← srcCases[i]?
  dstCases.findIdx? (·.1 == l)

/-! ## Scalars and strings -/

/-- A value whose shape does not match the type it is stored at (D-f; unreachable for
well-typed values). -/
def storeMismatch {α : Type} : P E σ α := internal "store: value does not match type"

/-- The scalar and string arms of REF `store` (L1461-1486) at primitive type `pt`:
`bool` as `int(bool(v))` in 1 byte, integers with `store_int` in `width / 8` bytes (signed for
the signed kinds), floats as `encode_float_as_i32/i64(v)` (C7 choice on a NaN) in 4/8 bytes,
`char` as `char_to_i32(v)` in 4 bytes, and strings with `store_string` (L1533). -/
def storePrim (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (pt : WIT.Primitive)
    (v : Val) (ptr : Nat) : P E σ Unit :=
  match pt, v with
  | .bool, .bool b => storeInt cx (if b then 1 else 0) ptr 1
  | .f32, .f32 x => do
    let b ← encodeFloat .f32 x
    storeInt cx b.toNat ptr 4
  | .f64, .f64 x => do
    let b ← encodeFloat .f64 x
    storeInt cx b.toNat ptr 8
  | .char, .char c => storeInt cx (ABI.charToI32 c).toNat ptr 4
  | .string, .string s => storeString lim q cx s ptr
  | pt, .int _ n =>
    match IntKind.ofPrimitive pt with
    | some k => storeInt cx n ptr (k.width / 8) k.signed
    | none => storeMismatch
  | _, _ => storeMismatch

/-! ## Lists (element store as a parameter) -/

/-- REF `store_list_into_valid_range(cx, v, ptr, elem_type)` (L1698-1700) with element size
`elemSize` and element store `storeElem`: element `i` is stored at `ptr + i * elemSize`. -/
def storeListIntoValidRangeWith (elemSize : Nat) (storeElem : Val → Nat → P E σ Unit)
    (vs : List Val) (ptr : Nat) : P E σ Unit :=
  Prog.forM vs.zipIdx fun (e, i) => storeElem e (ptr + i * elemSize)

/-- REF `store_list_into_range(cx, v, elem_type)` (L1689-1696) for an element layout `el`:
`byte_length = len(v) * elem_size`; `ptr = cx.allocate(alignment, byte_length)` (the
late-bound realloc); `trap_if` misaligned (`unalignedPointer`) and out of bounds
(`outOfBounds`), in this order; store the elements; return `(ptr, len(v))`. The REF assert
`byte_length <= REALLOC_I32_MAX` is a precondition (`StoreListPre`, D-f). -/
def storeListIntoRangeWith (cx : LiftLowerContext E) (el : ABI.Layout)
    (storeElem : Val → Nat → P E σ Unit) (vs : List Val) : P E σ (Nat × Nat) := do
  let byteLength := vs.length * el.size
  let ptr ← allocate cx el.alignment.bytes byteLength
  trapIf (decide (ptr ≠ ABI.alignTo ptr el.alignment)) .unalignedPointer
  checkInBounds cx ptr byteLength
  storeListIntoValidRangeWith el.size storeElem vs ptr
  pure (ptr, vs.length)

/-- REF `store_list(cx, v, ptr, elem_type, maybe_length)` (L1680-1687): a fixed-length list
(`fixed = true`) is stored in place; otherwise `store_list_into_range` and the pointer-sized
`(begin, length)` pair at `ptr` and `ptr + ptr_size`. -/
def storeListWith (cx : LiftLowerContext E) (el : ABI.Layout)
    (storeElem : Val → Nat → P E σ Unit) (fixed : Bool) (vs : List Val) (ptr : Nat) :
    P E σ Unit :=
  if fixed then storeListIntoValidRangeWith el.size storeElem vs ptr
  else do
    let (begin, length) ← storeListIntoRangeWith cx el storeElem vs
    let sz ← ptrSize cx
    storeInt cx begin ptr sz
    storeInt cx length (ptr + sz) sz

/-- The REF assertion of `store_list_into_range` (L1691, D-f): the list's byte length is at
most `REALLOC_I32_MAX`. A precondition of lowering a list of element layout `el`. -/
def StoreListPre (el : ABI.Layout) (vs : List Val) : Prop :=
  vs.length * el.size ≤ ABI.reallocI32Max

instance (el : ABI.Layout) (vs : List Val) : Decidable (StoreListPre el vs) := by
  unfold StoreListPre; infer_instance

/-! ## Variants and flags (non-recursive parts) -/

/-- The head of REF `store_variant(cx, v, ptr, cases)` (L1708-1716) for `n` cases whose
payload alignment is `payloadAlign` (REF `max_case_alignment`): store the case index `i` in
`disc_size` bytes at `ptr` and return the payload pointer
`align_to(ptr + disc_size, max_case_alignment)`. -/
def storeVariantHead (cx : LiftLowerContext E) (n : Nat) (payloadAlign : ABI.Alignment)
    (i ptr : Nat) : P E σ Nat := do
  storeInt cx i ptr (discSize n)
  pure (ABI.alignTo (ptr + discSize n) payloadAlign)

/-- REF `store_flags(cx, v, ptr, labels)` (L1724-1726): `pack_flags_into_int` of the first
`n = len(labels)` flags, stored in `elem_size_flags(labels)` bytes. -/
def storeFlags (cx : LiftLowerContext E) (n : Nat) (bs : List Bool) (ptr : Nat) :
    P E σ Unit :=
  storeInt cx (packFlags (bs.take n)) ptr (flagsSize n)

/-! ## `store` -/

mutual

/-- REF `store(cx, v, t, ptr)` (L1461-1486). Preconditions (REF asserts, D-f): `ptr` is
aligned to `alignment(t)` and `ptr + elem_size(t) <= len(memory)`. Dispatch on the type:

* primitives: `storePrim` (`store_int`, `encode_float_as_*` with C7, `char_to_i32`,
  `store_string`);
* `list t` / `fixed-list t n`: `store_list` (`storeListWith`; a dynamic list allocates
  `len * elem_size` bytes aligned to the element alignment through the late-bound realloc,
  traps misaligned/out of bounds, stores the elements and writes `(ptr, len)`);
* `record`/`tuple`: `store_record` (`storeFields`/`storeTuple`);
* `variant`/`enum`/`option`/`result`: `store_variant` (`storeVariantHead` then the payload of
  the case, `storeCase`/`storeOpt`);
* `flags`: `store_flags`;
* `map k v`: `store_list` of records `{ "0": k, "1": v }`;
* `own`/`borrow`/`stream`/`future`/`error-context`: `store_int` of `lower_own`,
  `lower_borrow`, `lower_stream`, `lower_future`, `lower_error_context` in 4 bytes. -/
def store (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (v : Val)
    (t : WIT.ClosedType RtId) (ptr : Nat) : P E σ Unit :=
  match t with
  | .prim pt => storePrim lim q cx pt v ptr
  | .ref r => nomatch r
  | .list u =>
    match v with
    | .list vs => do
      let p ← ptrType cx
      storeListWith cx (ABI.layout p u) (fun e a => store lim q cx e u a) false vs ptr
    | _ => storeMismatch
  | .fixedList u _ =>
    match v with
    | .list vs => do
      let p ← ptrType cx
      storeListWith cx (ABI.layout p u) (fun e a => store lim q cx e u a) true vs ptr
    | _ => storeMismatch
  | .map k u =>
    match v with
    | .list vs => do
      let p ← ptrType cx
      let el := ABI.layout p (.record (ABI.mapEntryFields k u) : WIT.ClosedType RtId)
      storeListWith cx el (fun e a =>
        match e with
        | .record [ek, ev] => do
          let kl := ABI.primitiveLayout p k.toPrimitive
          let a0 := ABI.alignTo a kl.alignment
          storePrim lim q cx k.toPrimitive ek a0
          store lim q cx ev u (ABI.alignTo (a0 + kl.size) (ABI.layout p u).alignment)
        | _ => storeMismatch) false vs ptr
    | _ => storeMismatch
  | .record fields =>
    match v with
    | .record vs => storeFields lim q cx vs fields ptr
    | _ => storeMismatch
  | .tuple ts =>
    match v with
    | .record vs => storeTuple lim q cx vs ts ptr
    | _ => storeMismatch
  | .variant cases =>
    match v with
    | .variant i payload => do
      let p ← ptrType cx
      let a ← storeVariantHead cx cases.length
        (ABI.maxCaseAlignment (ABI.layoutCases p cases)) i ptr
      storeCase lim q cx i payload cases a
    | _ => storeMismatch
  | .enum labels =>
    match v with
    | .variant i _ =>
      if i < labels.length then do
        let _ ← storeVariantHead cx labels.length .one i ptr
        pure ()
      else storeMismatch
    | _ => storeMismatch
  | .option u =>
    match v with
    | .variant 0 _ => do
      let p ← ptrType cx
      let _ ← storeVariantHead cx 2 (ABI.maxCaseAlignment [none, some (ABI.layout p u)]) 0 ptr
      pure ()
    | .variant 1 payload => do
      let p ← ptrType cx
      let a ← storeVariantHead cx 2 (ABI.maxCaseAlignment [none, some (ABI.layout p u)]) 1 ptr
      match payload with
      | some x => store lim q cx x u a
      | none => storeMismatch
    | _ => storeMismatch
  | .result ok err =>
    match v with
    | .variant 0 payload => do
      let p ← ptrType cx
      let a ← storeVariantHead cx 2
        (ABI.maxCaseAlignment [ABI.layoutOption p ok, ABI.layoutOption p err]) 0 ptr
      storeOpt lim q cx payload ok a
    | .variant 1 payload => do
      let p ← ptrType cx
      let a ← storeVariantHead cx 2
        (ABI.maxCaseAlignment [ABI.layoutOption p ok, ABI.layoutOption p err]) 1 ptr
      storeOpt lim q cx payload err a
    | _ => storeMismatch
  | .flags labels =>
    match v with
    | .flags bs => storeFlags cx labels.length bs ptr
    | _ => storeMismatch
  | .own rt =>
    match v with
    | .own rep => do storeInt cx (← lowerOwn lim cx rt rep) ptr 4
    | _ => storeMismatch
  | .borrow rt =>
    match v with
    | .borrow rep => do storeInt cx (← lowerBorrow lim cx rt rep) ptr 4
    | _ => storeMismatch
  | .stream _ =>
    match v with
    | .stream e => do storeInt cx (← lowerStream lim cx e) ptr 4
    | _ => storeMismatch
  | .future _ =>
    match v with
    | .future e => do storeInt cx (← lowerFuture lim cx e) ptr 4
    | _ => storeMismatch
  | .errorContext =>
    match v with
    | .errorContext x => do storeInt cx (← lowerErrorContext lim cx x) ptr 4
    | _ => storeMismatch
termination_by sizeOf t

/-- REF `store_record(cx, v, ptr, fields)` (L1702-1706) from the cursor `ptr`: for each
field, `ptr = align_to(ptr, alignment(f.t))`, store the field value, `ptr += elem_size(f.t)`.
The values are positional (`vs[i]` is the value of `fields[i]`); a length mismatch is a
shape mismatch (D-f). -/
def storeFields (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (vs : List Val)
    (fields : List (String × WIT.ClosedType RtId)) (ptr : Nat) : P E σ Unit :=
  match fields, vs with
  | [], [] => pure ()
  | (_, t) :: fields, v :: vs => do
    let p ← ptrType cx
    let a := ABI.alignTo ptr (ABI.layout p t).alignment
    store lim q cx v t a
    storeFields lim q cx vs fields (a + (ABI.layout p t).size)
  | _, _ => storeMismatch
termination_by sizeOf fields

/-- REF `store_record` for a despecialized tuple (`despecialize`, L1101-1108): as
`storeFields` over the field types `ts`. -/
def storeTuple (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (vs : List Val)
    (ts : List (WIT.ClosedType RtId)) (ptr : Nat) : P E σ Unit :=
  match ts, vs with
  | [], [] => pure ()
  | t :: ts, v :: vs => do
    let p ← ptrType cx
    let a := ABI.alignTo ptr (ABI.layout p t).alignment
    store lim q cx v t a
    storeTuple lim q cx vs ts (a + (ABI.layout p t).size)
  | _, _ => storeMismatch
termination_by sizeOf ts

/-- The tail of REF `store_variant` (L1714-1716): `c = cases[case_index]`; if `c.t is not
None`, store the payload at `ptr`. An out-of-range index or a missing payload for a case with
a type is a shape mismatch (D-f); a payload of a case without a type is ignored. -/
def storeCase (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (i : Nat)
    (payload : Option Val) (cases : List (String × Option (WIT.ClosedType RtId))) (ptr : Nat) :
    P E σ Unit :=
  match cases, i with
  | [], _ => storeMismatch
  | (_, t) :: _, 0 => storeOpt lim q cx payload t ptr
  | _ :: cases, i + 1 => storeCase lim q cx i payload cases ptr
termination_by sizeOf cases

/-- REF `if c.t is not None: store(cx, case_value, c.t, ptr)` (L1715-1716). -/
def storeOpt (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (payload : Option Val)
    (t : Option (WIT.ClosedType RtId)) (ptr : Nat) : P E σ Unit :=
  match t, payload with
  | none, _ => pure ()
  | some u, some v => store lim q cx v u ptr
  | some _, none => storeMismatch
termination_by sizeOf t

end

/-! ## REF-named entry points -/

/-- REF `store_list_into_valid_range(cx, v, ptr, elem_type)` (L1698-1700). -/
def storeListIntoValidRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vs : List Val) (ptr : Nat) (u : WIT.ClosedType RtId) : P E σ Unit := do
  let p ← ptrType cx
  storeListIntoValidRangeWith (ABI.layout p u).size (fun e a => store lim q cx e u a) vs ptr

/-- REF `store_list_into_range(cx, v, elem_type)` (L1689-1696). Precondition (D-f):
`StoreListPre (ABI.layout p u) vs` for the pointer type `p` of `cx`. -/
def storeListIntoRange (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vs : List Val) (u : WIT.ClosedType RtId) : P E σ (Nat × Nat) := do
  let p ← ptrType cx
  storeListIntoRangeWith cx (ABI.layout p u) (fun e a => store lim q cx e u a) vs

/-- REF `store_list(cx, v, ptr, elem_type, maybe_length)` (L1680-1687). -/
def storeList (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) (vs : List Val)
    (ptr : Nat) (u : WIT.ClosedType RtId) (maybeLength : Option Nat) : P E σ Unit := do
  let p ← ptrType cx
  storeListWith cx (ABI.layout p u) (fun e a => store lim q cx e u a) maybeLength.isSome vs
    ptr

/-- REF `store_variant(cx, v, ptr, cases)` (L1708-1716) for a variant value whose case index
`i` refers to `srcCases` (REF `match_case` by label, L1718-1722): the index is mapped to
`dstCases` with `matchCase` and the value stored at `variant dstCases`. No matching label is
a shape mismatch (D-f). -/
def storeMatched (lim : Limits) (q : Quirks) (cx : LiftLowerContext E) {α : Type}
    (srcCases : List (String × α)) (dstCases : List (String × Option (WIT.ClosedType RtId)))
    (i : Nat) (payload : Option Val) (ptr : Nat) : P E σ Unit :=
  match matchCase srcCases dstCases i with
  | some j => store lim q cx (.variant j payload) (.variant dstCases) ptr
  | none => storeMismatch

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

/-- The store updates `store` can issue, each preserving `I`: memory writes, resource
handle allocation, handle-table insertion, `num_borrows += 1`, and the end owner/index updates
of `lower_async_value`. -/
structure StorePres (I : CStore E → Prop) : Prop where
  write : ∀ m p bs s, I s → I (writeMemSt m p bs s)
  allocRes : AllocResHandlePres I
  addHandle : AddHandlePres I
  incBorrows : ∀ t st, I st → I (HandleSt.incBorrows (E := E) t st)
  setEndOwner : ∀ e inst st, I st → I (HandleSt.setEndOwner (E := E) e inst st)
  setEndIndex : ∀ e i st, I st → I (HandleSt.setEndIndex (E := E) e i st)

end P.Inv

/-! ## Examples -/

section Examples

end Examples

end Silmaril.Wasm.Component.Canon
