module

public import Silmaril.Wasm.Component.Reference.ABI.Despecialize.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Layout
public import Silmaril.Raw.Wasm.Component.ABI.Flatten

/-!
# Canonical ABI despecialization

Transcribes REF `despecialize` (component-model `a25fc0b`,
`design/mvp/canonical-abi/definitions.py` lines 1101–1108,
https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py):

* `tuple ts` becomes a `record` with labels `"0"`, `"1"`, … (Python `str(i)`);
* `enum labels` becomes a `variant` with no payloads;
* `option t` becomes `variant { none, some(t) }`;
* `result ok err` becomes `variant { ok(ok?), error(err?) }`;
* `map k v` becomes `list (record { "0": k, "1": v })`
  (REF `ListType(despecialize(TupleType([k,v])))`);
* every other type is unchanged.

Only the outermost constructor is rewritten, as in REF: each consumer despecializes at its
own entry. `string` and `flags` keep their special ABI and are not despecialized.

Proved here, for every closed type and both pointer widths: despecialization preserves the
memory layout (`layout_despecialize`) and the flattening (`flatten_despecialize`), and it is
idempotent (`despecialize_idem`). Nothing about the dynamic load/store behaviour is claimed.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

variable {Resource : Type u}

theorem despecialize_idem (t : WIT.ClosedType Resource) :
    despecialize (despecialize t) = despecialize t := by
  cases t <;> rfl

/-- The labels of a despecialized tuple are REF `str(i)`, `str(i+1)`, … -/
theorem tupleFieldsFrom_map_fst (i : Nat) (ts : List (WIT.ClosedType Resource)) :
    (tupleFieldsFrom i ts).map Prod.fst = (List.range' i ts.length).map toString := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih => simp only [tupleFieldsFrom, List.map_cons, List.length_cons,
      List.range'_succ, ih]

theorem layoutFields_tupleFieldsFrom (p : AddrType) (i : Nat)
    (ts : List (WIT.ClosedType Resource)) :
    layoutFields p (tupleFieldsFrom i ts) = layoutTypes p ts := by
  induction ts generalizing i with
  | nil => simp only [tupleFieldsFrom, layoutFields, layoutTypes]
  | cons t ts ih => simp only [tupleFieldsFrom, layoutFields, layoutTypes, ih]

theorem flattenFields_tupleFieldsFrom (p : AddrType) (i : Nat)
    (ts : List (WIT.ClosedType Resource)) :
    flattenFields p (tupleFieldsFrom i ts) = flattenTypes p ts := by
  induction ts generalizing i with
  | nil => simp only [tupleFieldsFrom, flattenFields, flattenTypes]
  | cons t ts ih => simp only [tupleFieldsFrom, flattenFields, flattenTypes, ih]

theorem layoutCases_enum (p : AddrType) (labels : List String) :
    layoutCases p (labels.map fun l => ((l, none) : String × Option (WIT.ClosedType Resource))) =
      List.replicate labels.length none := by
  induction labels with
  | nil => simp only [List.map_nil, layoutCases, List.length_nil, List.replicate_zero]
  | cons l ls ih =>
    simp only [List.map_cons, layoutCases, layoutOption, ih, List.length_cons,
      List.replicate_succ]

theorem flattenCases_enum (p : AddrType) (labels : List String) :
    flattenCases p (labels.map fun l => ((l, none) : String × Option (WIT.ClosedType Resource))) =
      List.replicate labels.length [] := by
  induction labels with
  | nil => simp only [List.map_nil, flattenCases, List.length_nil, List.replicate_zero]
  | cons l ls ih =>
    simp only [List.map_cons, flattenCases, flattenOption, ih, List.length_cons,
      List.replicate_succ]

theorem variantPayload_replicate_nil (n : Nat) :
    variantPayload (List.replicate n []) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, variantPayload, ih, joinFlat_nil_left]

/-- A payload-free variant has the layout of its discriminant. -/
theorem variantLayout_replicate_none (n : Nat) :
    variantLayout (List.replicate n none) = ⟨discriminantAlignment n, 1⟩ := by
  simp only [variantLayout, List.length_replicate, maxCaseAlignment_replicate_none,
    maxCaseSize_replicate_none, Nat.add_zero, Layout.rounded]
  generalize discriminantAlignment n = a
  cases a <;> decide

/-- REF computes `alignment`/`elem_size` of `despecialize(t)`; the direct layout of the
specialized form agrees. -/
theorem layout_despecialize (p : AddrType) (t : WIT.ClosedType Resource) :
    layout p (despecialize t) = layout p t := by
  cases t with
  | tuple ts => simp only [despecialize, layout, layoutFields_tupleFieldsFrom]
  | enum labels =>
    simp only [despecialize, layout, layoutCases_enum, variantLayout_replicate_none]
  | option t => simp only [despecialize, layout, layoutCases, layoutOption]
  | result ok err =>
    cases ok <;> cases err <;> simp only [despecialize, layout, layoutCases, layoutOption]
  | map k v => simp only [despecialize, layout]
  | _ => rfl

/-- Flattening is invariant under despecialization. -/
theorem flatten_despecialize (p : AddrType) (t : WIT.ClosedType Resource) :
    flatten p (despecialize t) = flatten p t := by
  cases t with
  | tuple ts => simp only [despecialize, flatten, flattenFields_tupleFieldsFrom]
  | enum labels =>
    simp only [despecialize, flatten, flattenCases_enum, variantPayload_replicate_nil]
  | option t =>
    simp only [despecialize, flatten, flattenCases, flattenOption, variantPayload,
      joinFlat_nil_left, joinFlat_nil_right]
  | result ok err =>
    simp only [despecialize, flatten, flattenCases, variantPayload, joinFlat_nil_right]
  | map k v => simp only [despecialize, flatten]
  | _ => rfl

/-! ## Tests -/

example : despecialize (.option (.prim .u8) : WIT.ClosedType Nat) =
    .variant [("none", none), ("some", some (.prim .u8))] := rfl

example : despecialize (.enum ["a", "b"] : WIT.ClosedType Nat) =
    .variant [("a", none), ("b", none)] := rfl

example : despecialize (.result (some (.prim .u32)) none : WIT.ClosedType Nat) =
    .variant [("ok", some (.prim .u32)), ("error", none)] := rfl

example : despecialize (.map .string (.prim .u64) : WIT.ClosedType Nat) =
    .list (.record [("0", .prim .string), ("1", .prim .u64)]) := rfl

example : despecialize (.flags ["a"] : WIT.ClosedType Nat) = .flags ["a"] := rfl

end Silmaril.Wasm.Component.ABI
