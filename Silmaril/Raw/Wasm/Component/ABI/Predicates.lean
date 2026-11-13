module

public import Silmaril.Wasm.Component.Reference.ABI.Predicates.Defs

public import Silmaril.Raw.Wasm.Component.ABI.Despecialize
public import Silmaril.Raw.Wasm.Component.WIT.Package

/-!
# Canonical ABI type predicates

* Decidable equality for `WIT.ValType Ref Resource` and `WIT.FuncType Ref Resource` (the
  derive handler does not apply to the nested inductive outside its defining module, so a
  structural `ValType.beq` is proved lawful and the instance is built from it).
* REF `contains`, `contains_borrow`, `contains_async_value` and `none_or_number_type`
  (component-model `a25fc0b`, `design/mvp/canonical-abi/definitions.py` lines 1112–1140,
  https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py).
  `contains p t` applies `p` to `despecialize t` and recurses into the children of the
  despecialized form, exactly as REF does, so `p` never sees a tuple, enum, option, result or
  map (`contains_despecialize`). Deviation D-c: REF's `contains` hits `assert(False)` on
  `flags` and `error-context`; here they are leaves (`p t`).
* `containsListOrString`: the `CanonicalABI.md` §Canonical Definitions side condition
  "requires `memory`/`realloc` if `T` contains a `list` or `string`". A dynamic `list` (and
  hence a `map`, which despecializes to one) or a `string` counts; a fixed-length list stores
  its elements inline and counts only through its element type (as wasmparser's
  `contains_ptr`).
* Syntactic feature-usage predicates `ValType.usesFixedList/usesMap/usesErrorContext/
  usesAsyncValue` (deep, over the undespecialized syntax), consumed by validation and profiles.
* `ValType.WellFormedCM`: the component-model value-type rules of `Binary.md` §Type
  Definitions, applied to every nested value type: structural
  `WIT.ValType.WellFormed` (nonempty labels, flags `1..32`, fixed length `> 0`); every record
  field, variant case, enum case and flag label is a kebab-case `label` (`WIT.IsLabel`) and the
  labels of each type are strongly unique (`Explainer.md` §Name Uniqueness, `WIT.canonLabel`:
  hyphens removed, lowercased); no `borrow` inside `stream`/`future` elements; no
  `stream<char>`; and `elem_size(u, 'i64') < 2^28` for every subterm `u` (each nested type is
  its own `defvaltype` in the binary). Not feature-gated (gating is validation's job).
  `FuncType.WellFormedCM`: parameter names are labels and strongly unique, parameter and result
  types satisfy `ValType.WellFormedCM`, and the result contains no `borrow`.

Not modelled: REF `contains` on a `FuncType` (shallow, only used by the host-facing
`canon_lift`/`canon_lower` asserts); resource-type validity (resources are opaque here).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v w

section DecEq

variable {Ref : Type u} {Res : Type v} [DecidableEq Ref] [DecidableEq Res]

end DecEq

/-! ## Decidability of structural well-formedness -/

section WellFormed

variable {Ref : Type u} {Res : Type v} (refOk : Ref → Prop) (resOk : Res → Prop)
  [DecidablePred refOk] [DecidablePred resOk]

end WellFormed

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Component.ABI

universe u

variable {R : Type u}

open WIT

/-! ## REF `contains` and derived predicates -/

theorem containsFields_tupleFieldsFrom (p : ClosedType R → Bool) (i : Nat)
    (ts : List (ClosedType R)) : containsFields p (tupleFieldsFrom i ts) = containsList p ts := by
  induction ts generalizing i with
  | nil => simp only [tupleFieldsFrom, containsFields, containsList]
  | cons t ts ih => simp only [tupleFieldsFrom, containsFields, containsList, ih]

theorem containsCases_enum (p : ClosedType R → Bool) (ls : List String) :
    containsCases p (ls.map fun l => ((l, none) : String × Option (ClosedType R))) = false := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, containsCases, containsOpt, ih, Bool.or_self]

/-- `contains` only ever inspects despecialized types, so despecializing first is a no-op
(REF performs `t = despecialize(t)` on entry). -/
theorem contains_despecialize (p : ClosedType R → Bool) (t : ClosedType R) :
    contains p (despecialize t) = contains p t := by
  cases t with
  | ref e => exact e.elim
  | tuple ts => simp only [despecialize, contains, containsFields_tupleFieldsFrom]
  | enum ls => simp only [despecialize, contains, containsCases_enum, Bool.or_false]
  | option u =>
    simp only [despecialize, contains, containsCases, containsOpt, Bool.false_or, Bool.or_false]
  | result a b => simp only [despecialize, contains, containsCases, Bool.or_false]
  | map k v =>
    simp only [despecialize, contains, mapEntryFields, containsFields, Bool.or_false]
  | _ => rfl

/-- `contains p t` holds whenever `p` holds of the despecialized `t` itself. -/
theorem contains_of_pred {p : ClosedType R → Bool} {t : ClosedType R}
    (h : p (despecialize t) = true) : contains p t = true := by
  cases t with
  | ref e => exact e.elim
  | _ => simp_all [contains, despecialize]

/-! ## Syntactic feature usage -/

/-! ## Component-model well-formedness -/

/-! ## Tests -/

private abbrev Ty := ClosedType Nat

/-- Tuple labels are REF `str(i)` in general by `tupleFieldsFrom_map_fst`; this instance
checks the shape (`Nat.repr` does not reduce in the kernel, so the labels stay `toString i`). -/
example : despecialize (.tuple [.prim .u8, .prim .u16] : Ty) =
    .record [(toString 0, .prim .u8), (toString 1, .prim .u16)] := rfl

example : despecialize (.option (.prim .u8) : Ty) =
    .variant [("none", none), ("some", some (.prim .u8))] := by decide +kernel

example : containsBorrow (.record [("a", .borrow 0)] : Ty) = true := by decide +kernel

example : containsBorrow (.option (.own 3) : Ty) = false := by decide +kernel

example : containsAsyncValue (.map .u8 (.future none) : Ty) = true := by decide +kernel

example : containsListOrString (.fixedList (.prim .u32) 4 : Ty) = false := by decide +kernel

example : containsListOrString (.map .u8 (.prim .u32) : Ty) = true := by decide +kernel

example : noneOrNumberType (some (.prim .f32) : Option Ty) = true := by decide +kernel

example : noneOrNumberType (some (.prim .char) : Option Ty) = false := by decide +kernel

example : ValType.usesMap (.list (.map .u8 (.prim .u8)) : Ty) = true := by decide +kernel

example : ValType.usesFixedList (.list (.map .u8 (.prim .u8)) : Ty) = false := by decide +kernel

example : ¬ ValType.WellFormedCM (.stream (some (.prim .char)) : Ty) := by decide +kernel

example : ¬ ValType.WellFormedCM (.flags ((List.range 33).map toString) : Ty) := by
  decide +kernel

example : ¬ ValType.WellFormedCM (.future (some (.borrow 0)) : Ty) := by decide +kernel

example : ValType.WellFormedCM (.option (.prim .u8) : Ty) := by decide +kernel

example : ¬ ValType.WellFormedCM (.fixedList (.prim .u64) (2 ^ 25) : Ty) := by decide +kernel

example : ¬ ValType.WellFormedCM (.list (.fixedList (.prim .u8) (2 ^ 30)) : Ty) := by
  decide +kernel

example : ¬ ValType.WellFormedCM (.stream (some (.fixedList (.prim .u8) (2 ^ 30))) : Ty) := by
  decide +kernel

example : ¬ ValType.WellFormedCM (.record [("a-b", .prim .u8), ("ab", .prim .u8)] : Ty) := by
  decide +kernel

example : ¬ ValType.WellFormedCM (.option (.enum ["a-b", "AB"]) : Ty) := by decide +kernel

example : ¬ ValType.WellFormedCM (.record [("Not A Label!", .prim .u8)] : Ty) := by
  decide +kernel

example : ValType.WellFormedCM (.record [("a-b", .prim .u8), ("c", .flags ["x", "y"])] : Ty) := by
  decide +kernel

example : ¬ FuncType.WellFormedCM
    (⟨[("a-b", .prim .u8), ("ab", .prim .u8)], none, false⟩ : WIT.FuncType Empty Nat) := by
  decide +kernel

example : FuncType.WellFormedCM
    (⟨[("a-b", .prim .u8), ("c", .prim .u8)], some (.prim .u32), false⟩ :
      WIT.FuncType Empty Nat) := by
  decide +kernel

example : ¬ FuncType.WellFormedCM ({ params := [], result := some (.borrow 0) } :
    WIT.FuncType Empty Nat) := by decide +kernel

end Silmaril.Wasm.Component.ABI
