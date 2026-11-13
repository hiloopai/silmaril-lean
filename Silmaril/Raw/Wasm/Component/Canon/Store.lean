module

public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs

public import Silmaril.Raw.Wasm.Component.Canon.Strings
public import Silmaril.Raw.Wasm.Component.Canon.Scalar
public import Silmaril.Raw.Wasm.Component.Canon.Handles
public import Silmaril.Raw.Wasm.Component.ABI.Despecialize
public import Silmaril.Raw.Wasm.Component.Value.Typing

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

theorem packFlags_lt (bs : List Bool) : packFlags bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp only [packFlags, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem findIdx?_label_nodup {β : Type} (l : String) :
    ∀ (cs : List (String × β)) (i : Nat), (cs.map Prod.fst).Nodup →
      (cs.map Prod.fst)[i]? = some l → cs.findIdx? (·.1 == l) = some i
  | [], _, _, h => by simp at h
  | c :: cs, 0, _, h => by
    simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h
    simp [List.findIdx?_cons, h]
  | c :: cs, i + 1, hnd, h => by
    simp only [List.map_cons, List.getElem?_cons_succ] at h
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hne : c.1 ≠ l := by
      intro hc; subst hc; exact hnd.1 (List.mem_of_getElem? h)
    rw [List.findIdx?_cons]
    simp only [beq_iff_eq, hne, ite_false, findIdx?_label_nodup l cs i hnd.2 h,
      Option.map_some]

/-- On a type with distinct labels, `match_case` against the same cases is the identity on
in-range indices. -/
theorem matchCase_self {β : Type} (cs : List (String × β)) (hnd : (cs.map Prod.fst).Nodup)
    (i : Nat) (hi : i < cs.length) : matchCase cs cs i = some i := by
  have hg : cs[i]? = some cs[i] := List.getElem?_eq_getElem hi
  have hl : (cs.map Prod.fst)[i]? = some cs[i].1 := by simp [hg]
  simp only [matchCase, hg, Option.bind_eq_bind, Option.bind_some]
  exact findIdx?_label_nodup _ cs i hnd hl

example : matchCase [("a", ()), ("b", ())] [("b", ()), ("a", ())] 0 = some 1 := by decide
example : matchCase [("a", ()), ("c", ())] [("b", ()), ("a", ())] 1 = none := by decide

/-! ## Scalars and strings -/

/-! ## Lists (element store as a parameter) -/

/-! ## Variants and flags (non-recursive parts) -/

/-! ## `store` -/

/-! ## REF-named entry points -/

/-! ## Invariant lemmas -/

namespace P.Inv

variable {I : CStore E → Prop}

theorem storeMatched (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    {α : Type} (srcCases : List (String × α))
    (dstCases : List (String × Option (WIT.ClosedType RtId))) (i : Nat)
    (payload : Option Val) (ptr : Nat) :
    P.Inv I (Canon.storeMatched lim q cx srcCases dstCases i payload ptr : P E σ Unit) := by
  unfold Canon.storeMatched
  split
  · exact store h _ _ _ _ _ _
  · exact storeMismatch

theorem storeList (h : StorePres I) (lim : Limits) (q : Quirks) (cx : LiftLowerContext E)
    (vs : List Val) (ptr : Nat) (u : WIT.ClosedType RtId) (m : Option Nat) :
    P.Inv I (Canon.storeList lim q cx vs ptr u m : P E σ Unit) :=
  bind (ptrType cx) fun _ =>
    storeListWith _ _ (fun e a => store h lim q cx e u a) _ _ _ h.write

end P.Inv

/-! ## Examples -/

section Examples

/-- Lowering a `list<u8>` of two elements: one realloc of 2 bytes aligned to 1, then two
`store_int`s and the `(ptr, len)` pair. -/
example (cx : LiftLowerContext E) (ptr : Nat) : P E σ Unit :=
  store Limits.spec Quirks.none cx (.list [.int .u8 1, .int .u8 2]) (.list (.prim .u8)) ptr

/-- Lowering an `option<f32>` holding a NaN issues the C7 choice when the payload is
stored. -/
example (cx : LiftLowerContext E) (ptr : Nat) : P E σ Unit :=
  store Limits.spec Quirks.none cx (.variant 1 (some (.f32 0x7fc00001#32)))
    (.option (.prim .f32)) ptr

/-- A variant lifted at `{a, b}` lowered into `{b, a}` by label. -/
example (cx : LiftLowerContext E) (ptr : Nat) : P E σ Unit :=
  storeMatched Limits.spec Quirks.none cx [("a", ()), ("b", ())]
    [("b", none), ("a", some (.prim .u32))] 0 (some (.int .u32 7)) ptr

example : discSize 256 = 1 ∧ discSize 257 = 2 ∧ discSize 65537 = 4 := by decide
example : packFlags [true, false, true] = 5 := by decide
example : flagsSize 9 = 2 := by decide

end Examples

end Silmaril.Wasm.Component.Canon
