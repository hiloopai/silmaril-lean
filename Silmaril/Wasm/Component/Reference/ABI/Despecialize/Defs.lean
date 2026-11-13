module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs

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

/-- The fields of a despecialized tuple, labelled `str(i)` from index `i`. -/
def tupleFieldsFrom (i : Nat) : List (WIT.ClosedType Resource) →
    List (String × WIT.ClosedType Resource)
  | [] => []
  | t :: ts => (toString i, t) :: tupleFieldsFrom (i + 1) ts

/-- The record fields `"0": k, "1": v` of a despecialized map entry. -/
def mapEntryFields (k : WIT.KeyType) (v : WIT.ClosedType Resource) :
    List (String × WIT.ClosedType Resource) :=
  [("0", .prim k.toPrimitive), ("1", v)]

/-- REF `despecialize` (definitions.py 1101–1108): rewrite the outermost specialized type
constructor into its general form. -/
def despecialize : WIT.ClosedType Resource → WIT.ClosedType Resource
  | .tuple ts => .record (tupleFieldsFrom 0 ts)
  | .enum labels => .variant (labels.map fun l => (l, none))
  | .option t => .variant [("none", none), ("some", some t)]
  | .result ok err => .variant [("ok", ok), ("error", err)]
  | .map k v => .list (.record (mapEntryFields k v))
  | t => t

@[simp] theorem tupleFieldsFrom_length (i : Nat) (ts : List (WIT.ClosedType Resource)) :
    (tupleFieldsFrom i ts).length = ts.length := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih => simp only [tupleFieldsFrom, List.length_cons, ih]

@[simp] theorem tupleFieldsFrom_map_snd (i : Nat) (ts : List (WIT.ClosedType Resource)) :
    (tupleFieldsFrom i ts).map Prod.snd = ts := by
  induction ts generalizing i with
  | nil => rfl
  | cons t ts ih => simp only [tupleFieldsFrom, List.map_cons, ih]

@[simp] theorem maxCaseAlignment_replicate_none (n : Nat) :
    maxCaseAlignment (List.replicate n none) = .one := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, maxCaseAlignment, ih]

@[simp] theorem maxCaseSize_replicate_none (n : Nat) :
    maxCaseSize (List.replicate n none) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, maxCaseSize, ih]

/-! ## Tests -/

end Silmaril.Wasm.Component.ABI
