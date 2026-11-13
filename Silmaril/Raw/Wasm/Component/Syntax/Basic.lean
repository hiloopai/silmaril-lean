module

public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs

public import Silmaril.Wasm.Types
public import Silmaril.Raw.Wasm.Component.ABI.String

/-!
# Component syntax: the index-based, core-parametric AST

The abstract syntax of a component as it stands after `flatten(sections)` of the binary format:
an ordered list of definitions that refer to earlier definitions by index. The AST transcribes
the grammar of `design/mvp/Binary.md` at component-model revision `a25fc0b`
(https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/Binary.md),
§Component Definitions, §Instance Definitions, §Alias Definitions, §Type Definitions,
§Canonical Definitions, §🪙 Start Definitions, §Import and Export Definitions and §🪙 Value
Definitions, with the prose of `Explainer.md` at the same revision.

It is parametric in the core module type `M`, so `Component Lime1.Module`,
`Component V1.Module` and `Component Silmaril.Wasm.Module` are all instances; `Component.map`
embeds one into another, and `Component.coreModules` lists every (nested) core module in order.
Core *types* that occur inside components (core module types, the `core:rectype` definitions,
the function type of `thread.new-indirect`) always use the Core 3.0 syntax
`Silmaril.Wasm.RecType` / `Silmaril.Wasm.ExternType`; profiles restrict them later.

| Lean | `Binary.md` production |
| --- | --- |
| `CoreSort`, `Sort_`, `SortIdx` | `core:sort`, `sort`, `sortidx`, `core:sortidx` |
| `CoreInstanceExpr`, `InstanceExpr` | `core:instanceexpr`, `instanceexpr` |
| `Alias` | `alias` |
| `CoreModuleDecl`, `CoreTypeDef` | `core:moduledecl`, `core:deftype` |
| `Prim`, `VT`, `DefValType` | `primvaltype`, `valtype`, `defvaltype` |
| `FuncType`, `TypeBound`, `ValueBound` | `functype`, `typebound`, `valuebound` |
| `ExternDesc` | `externtype` |
| `DefType` | `deftype`, including `resourcetype` |
| `InstanceDecl`, `ComponentDecl` | `instancedecl`, `componentdecl` |
| `Attribute`, `ExternName` | `attribute`, `nameattributes` |
| `CanonOpt`, `Builtin`, `Canon` | `canonopt`, `canon` |
| `Definition`, `Component` | `definition` (Explainer §Component Definitions), `component` |

Representation choices (not claims about the binary format):
* Keywords are suffixed with `_` (`Sort_`, `module_`, `instance_`, `import_`, `export_`,
  `async_`, `rec_`); `Sort` itself is a Lean keyword, hence `Sort_`.
* Binary-only warts are dropped: the duplicate `0x00`/`0x01` forms of `nameattributes`, the
  `0x00` prefix of a non-final `sub` core type (it is an ordinary one-element `RecType`), the
  `0x00` sort byte of `canon lift`/`lower`, and the reserved `0x00` byte of `thread.yield`,
  `thread.suspend` and `thread.*-then-*`. `waitable-set.wait`/`poll` keep only their memory
  index. Custom sections and the name section are not represented.
* `canonopt` string encodings reuse `ABI.StringEncoding` (the runtime's type).
* `resourcetype`'s `rep` core value type is an `AddrType` (`i32`, or `i64` under 🐘), as are the
  core value types of `context.get`/`context.set`; other core value types are not
  representable there.
* 🪙 `value` definitions carry their type and the opaque binary payload `val(t)` (bytes).
* `stream.read`/`write` and `future.read`/`write` carry the full `opts`; whether they are sync
  or async is the presence of the `async` option (sync forms are gated by 🚝).

Not modelled: text format sugar and identifiers, binary decoding, the 🧵② builtins
`thread.spawn-ref`, `thread.spawn-indirect`, `thread.available-parallelism`, and 🪺 is only
present as far as names are strings. No well-formedness or validation is claimed here: every
side condition of `Binary.md` (non-empty records, `flags` bound, `fixedList` length > 0,
option compatibility, index ranges, ...) belongs to validation.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Syntax

/-! ## Sorts and indices -/

/-! ## Instances and aliases -/

/-! ## Names -/

/-! ## Core types -/

/-! ## Component types -/

/-! The deriving handler does not support nested inductives, so decidable equality of the
declarator types (and of `Definition` below) goes through a structural Boolean equality, which
reduces in the kernel, and its correctness proof. -/

/-! ## Canonical definitions -/

/-! ## Definitions and components -/

variable {M N P : Type}

section DecEq

variable [DecidableEq M]

end DecEq

/-! ## Changing the core module type -/

theorem Definition.mapList_eq (f : M → N) (ds : List (Definition M)) :
    Definition.mapList f ds = ds.map (Definition.map f) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [Definition.mapList, List.map_cons, ih]

theorem Definition.coreModulesList_eq (ds : List (Definition M)) :
    Definition.coreModulesList ds = (ds.map Definition.coreModules).flatten := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [Definition.coreModulesList, List.map_cons, List.flatten_cons, ih]

mutual

theorem Definition.map_comp (f : M → N) (g : N → P) :
    (d : Definition M) → Definition.map g (Definition.map f d) = Definition.map (g ∘ f) d
  | .coreModule _ | .coreInstance _ | .coreType _ | .instance_ _ | .alias _ | .type _
  | .canon _ | .start _ _ _ | .import_ _ _ | .export_ _ _ _ | .value _ _ => rfl
  | .component defs => by
    simp only [Definition.map, Definition.mapList_comp f g defs]

theorem Definition.mapList_comp (f : M → N) (g : N → P) :
    (ds : List (Definition M)) →
      Definition.mapList g (Definition.mapList f ds) = Definition.mapList (g ∘ f) ds
  | [] => rfl
  | d :: ds => by
    simp only [Definition.mapList, Definition.map_comp f g d, Definition.mapList_comp f g ds]

end

set_option linter.dupNamespace false in
theorem Component.map_comp (f : M → N) (g : N → P) (c : Component M) :
    Component.map g (Component.map f c) = Component.map (g ∘ f) c :=
  Definition.mapList_comp f g c

set_option linter.dupNamespace false in
theorem Component.map_eq_list_map (f : M → N) (c : Component M) :
    Component.map f c = List.map (Definition.map f) c :=
  Definition.mapList_eq f c

example : Component.coreModules
    ([.coreModule 1, .component [.coreModule 2, .component [.coreModule 3]], .coreModule 4] :
      Component Nat) = [1, 2, 3, 4] := by decide +kernel

example : Component.map (· + 1)
    ([.coreModule 1, .component [.coreModule 2, .type (.resource .i32 none)]] : Component Nat) =
      [.coreModule 2, .component [.coreModule 3, .type (.resource .i32 none)]] := by decide +kernel

example : (DefType.instance_ [.export_ { name := "f" } (.func 0)]) ≠
    DefType.instance_ [.export_ { name := "g" } (.func 0)] := by decide +kernel

example : ([.component [.coreModule 1]] : Component Nat) ≠ [.component [.coreModule 2]] := by
  decide +kernel

end Silmaril.Wasm.Component.Syntax
