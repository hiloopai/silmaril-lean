module

public import Silmaril.Wasm.Component.Engine.Interface

/-!
# The static part of a core engine

A core engine (`CoreEngine`) has a static part, its module, type and address types, and a
store-dependent part, the store family and every operation that takes a store
(`Engine.Sim`). Component-level runtime data mentions only the static part: canonical options
hold memory and function addresses, tasks and callers hold options, item values hold modules
and extern values.

* `CoreEngine.Static`: the types such data uses, with decidable equality of addresses.
* `CoreEngine.toStatic E`: the static part of `E`, also a coercion. It is reducible, so
  `E.toStatic.FuncAddr` is `E.FuncAddr` for instance search and `simp`.

The data types of the component runtime (`Runtime.CanonOpts`, `CanonHost`, `Task`, `Caller`,
`Canon.Call`, `Canon.Ret`, `Instantiate.ItemVal`, …) are indexed by `CoreEngine.Static`. Two
engines with the same static part, such as `E` and `E.withStore I`, therefore have the same
types of such data by definition: `CanonHost (E.withStore I)` and `CanonHost E` are both
`CanonHost E.toStatic` up to unfolding. This is what lets a store map relate the component
stores of the two engines (`Machine.Transfer`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

/-- The static part of a core engine that component-level data refers to. -/
structure CoreEngine.Static where
  /-- Core modules. -/
  Module : Type
  /-- Core extern types. -/
  ExternType : Type
  /-- Function addresses. -/
  FuncAddr : Type
  /-- Memory addresses. -/
  MemAddr : Type
  /-- Table addresses. -/
  TableAddr : Type
  [decEqFuncAddr : DecidableEq FuncAddr]
  [decEqMemAddr : DecidableEq MemAddr]
  [decEqTableAddr : DecidableEq TableAddr]
  /-- External values. -/
  ExternVal : Type

attribute [instance] CoreEngine.Static.decEqFuncAddr CoreEngine.Static.decEqMemAddr
  CoreEngine.Static.decEqTableAddr

/-- The static part of `E`. -/
@[reducible] def CoreEngine.toStatic (E : CoreEngine) : CoreEngine.Static where
  Module := E.Module
  ExternType := E.ExternType
  FuncAddr := E.FuncAddr
  MemAddr := E.MemAddr
  TableAddr := E.TableAddr
  ExternVal := E.ExternVal

instance : Coe CoreEngine CoreEngine.Static := ⟨CoreEngine.toStatic⟩

end Silmaril.Wasm.Component.Engine
