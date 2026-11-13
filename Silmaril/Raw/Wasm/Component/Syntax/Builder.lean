module

public import Silmaril.Wasm.Component.Reference.Syntax.Builder.Defs

public import Silmaril.Raw.Wasm.Component.Syntax.Basic
public import Silmaril.Wasm.Lime1.Modules

/-!
# A builder DSL for component definitions

Small, total helpers for writing example components compactly as `Component Lime1.Module`
(or `Component M` for any core module type `M`), together with `Component.nextIndex`, which
computes the next free index of every index space so that authors do not miscount indices.

The index-space bookkeeping transcribes `Explainer.md` §Index Spaces and `Binary.md` at
component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md):
every definition appends to exactly one index space, and in particular

* `canon lift` defines a component `func`; `canon lower` and every canon builtin define a
  core `func`;
* an alias appends to the sort it names (`alias core export` to a core sort);
* an `import` appends to the sort of its descriptor, and **every export introduces a new
  index** of the exported sort (`Binary.md` §Import and Export Definitions, note 1);
* a core `type` definition that is a recursion group appends one core type per sub type
  (Core 3.0 `rectype`); a core module type appends one;
* 🪙 `start f args results` appends `results` values (`Binary.md` §Start Definitions), and
  🪙 `value` appends one value.

Definitions inside nested `component` definitions live in their own index spaces and are not
counted by the enclosing component's `nextIndex`.

Tests: `nextIndex` is checked by `rfl` on three examples assembled from `Explainer.md`
(§Component Definitions, §Instance Definitions, §Canonical ABI): the adder, the simple
async-callback component, and the two-component linking example. The examples are syntax only: no
validation or typing of them is claimed here. -/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

variable {M : Type}

/-! ## Value type shorthands -/

namespace VT

end VT

/-! ## Sort-index shorthands -/

namespace SortIdx

end SortIdx

/-! ## Type shorthands -/

/-! ## Instances and aliases -/

/-! ## Canonical definitions -/

/-! ## Imports and exports -/

/-! ## Index spaces -/

section NextIndex

set_option linter.dupNamespace false

theorem Component.nextIndex_append (s : Sort_) (c c' : Component M) :
    Component.nextIndex s (c ++ c') = Component.nextIndex s c + Component.nextIndex s c' := by
  induction c with
  | nil => simp
  | cons d ds ih => simp only [List.cons_append, Component.nextIndex_cons, ih, Nat.add_assoc]

/-- Appending one definition bumps exactly its own index space, by `Definition.count`. -/
theorem Component.nextIndex_concat (s : Sort_) (c : Component M) (d : Definition M) :
    Component.nextIndex s (c ++ [d]) =
      Component.nextIndex s c + if d.sort = s then d.count else 0 := by
  simp [Component.nextIndex_append, Definition.added]

/-- `nextIndex` only depends on the index-space structure, not on the core modules. -/
theorem Component.nextIndex_map {N : Type} (f : M → N) (s : Sort_) (c : Component M) :
    Component.nextIndex s (Component.map f c) = Component.nextIndex s c := by
  rw [Component.map_eq_list_map]
  induction c with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, Component.nextIndex_cons, ih]
    congr 1
    cases d <;> first | rfl | (rename_i x; cases x <;> rfl)

end NextIndex

/-! ## Examples (assembled from `Explainer.md`) -/

namespace BuilderExamples

theorem adder_nextIndex (m : M) :
    (adder m).nextIndex (.core .module_) = 1 ∧ (adder m).nextIndex (.core .instance_) = 1 ∧
    (adder m).nextIndex (.core .func) = 1 ∧ (adder m).nextIndex .type = 1 ∧
    (adder m).nextIndex .func = 2 ∧ (adder m).nextIndex .instance_ = 0 ∧
    (adder m).nextIndex .component = 0 ∧ (adder m).nextIndex .value = 0 ∧
    (adder m).nextIndex (.core .type) = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem adderLime1_nextIndex :
    adderLime1.nextIndex .func = 2 ∧ adderLime1.nextIndex (.core .func) = 1 ∧
    adderLime1.nextIndex .type = 1 := ⟨rfl, rfl, rfl⟩

theorem adderLime1_coreModules : adderLime1.coreModules = [adderCore] := rfl

theorem asyncRun_nextIndex (m : M) :
    (asyncRun m).nextIndex (.core .module_) = 1 ∧ (asyncRun m).nextIndex (.core .func) = 3 ∧
    (asyncRun m).nextIndex (.core .instance_) = 2 ∧ (asyncRun m).nextIndex .type = 1 ∧
    (asyncRun m).nextIndex .func = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem linkB_nextIndex (n : M) :
    (linkB n).nextIndex .type = 2 ∧ (linkB n).nextIndex .instance_ = 1 ∧
    (linkB n).nextIndex .func = 3 ∧ (linkB n).nextIndex (.core .func) = 2 ∧
    (linkB n).nextIndex (.core .module_) = 1 ∧ (linkB n).nextIndex (.core .instance_) = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem linkP_nextIndex (m n : M) :
    (linkP m n).nextIndex .component = 2 ∧ (linkP m n).nextIndex .instance_ = 2 ∧
    (linkP m n).nextIndex .func = 2 ∧ (linkP m n).nextIndex (.core .module_) = 0 ∧
    (linkP m n).coreModules = [m, n] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Core Wasm 3.0 recursion groups define one core type per sub type; a resource type, an
import of a `(sub resource)` type and its export each add one component type index; a 🪙
`start` adds one value per result. -/
example (t₁ t₂ : Silmaril.Wasm.SubType) :
    Component.nextIndex (.core .type)
      ([.coreType (.rec_ ⟨[t₁, t₂]⟩), .coreType (.module_ [])] : Component M) = 3 ∧
    Component.nextIndex .type
      ([resourceT, importResource "r", exportType "r" 1] : Component M) = 3 ∧
    Component.nextIndex .value ([.start 0 [] 2, .value .u32 []] : Component M) = 3 :=
  ⟨rfl, rfl, rfl⟩

end BuilderExamples

end Silmaril.Wasm.Component.Syntax
