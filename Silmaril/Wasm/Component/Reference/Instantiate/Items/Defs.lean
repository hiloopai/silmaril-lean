module

public import Silmaril.Wasm.Component.Reference.Runtime.Ids.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Value.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs
public import Silmaril.Wasm.Component.Engine.Interface

/-!
# Instantiation-time item values, closures and frames

The run-time values of the component index spaces during instantiation (Explainer.md, "Index
Spaces" and "Instance Definitions"): `ItemVal E`, `Closure E` and `Frame E`, one mutual nested
block, and the empty frame. There is no upstream function for this (the Python reference
`definitions.py` at component-model `a25fc0b` has no instantiation); it corresponds to the
`*Def` item values of wasmtime's inliner (`crates/environ/src/component/translate/inline.rs` at
wasmtime `a7b4f29`).

This file is deliberately light: it is imported by `Canon/Effects.lean` (the late-bound call
`Call.instantiate` and its result `Ret.items` carry item values), so it must not bring
core-syntax modules such as `Silmaril.Wasm.Modules` into scope (their `Silmaril.Wasm.Table`
would shadow `Runtime.Table` in every `Silmaril.Wasm.Component` namespace). Lookups, resolution
and type computations are in `Instantiate/Runtime.lean`.

Not claimed: anything; this file only defines data.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Instantiate

open Engine _root_.Silmaril.Wasm.Component.Runtime
open _root_.Silmaril.Wasm.Component.Validation (CoreTypeSlot)

/-! ## Run-time item values, closures and frames -/

mutual

/-- The run-time value of a component-level index entry (Explainer.md, "Index Spaces"). -/
inductive ItemVal (E : CoreEngine) where
  /-- A core module (static code). -/
  | coreModule (m : E.Module)
  /-- A component function. -/
  | func (f : FuncId)
  /-- 🪙 A component value. -/
  | value (v : Value.Val)
  /-- A run-time type: resource variables are resource-type identities. -/
  | type (t : Types.TypeDef RtId E.ExternType)
  /-- A component instance: its export map. -/
  | «instance» (exports : List (String × ItemVal E))
  /-- A component: a closure. -/
  | component (c : Closure E)

/-- A component closure: the definitions and the captured enclosing frames, innermost
first (the targets of `alias outer`). -/
structure Closure (E : CoreEngine) where
  body : Syntax.Component E.Module
  outer : List (Frame E)

/-- The index spaces of one component scope at run time. -/
structure Frame (E : CoreEngine) where
  coreFuncs : List E.FuncAddr
  coreTables : List E.ExternVal
  coreMems : List E.ExternVal
  coreGlobals : List E.ExternVal
  coreTags : List E.ExternVal
  coreTypes : List (CoreTypeSlot E.ExternType)
  coreModules : List E.Module
  coreInstances : List (List (String × E.ExternVal))
  funcs : List FuncId
  values : List Value.Val
  types : List (Types.TypeDef RtId E.ExternType)
  instances : List (List (String × ItemVal E))
  components : List (Closure E)

end

variable {E : CoreEngine}

/-- The empty frame (the index spaces of a component before its first definition). -/
def Frame.empty : Frame E where
  coreFuncs := []
  coreTables := []
  coreMems := []
  coreGlobals := []
  coreTags := []
  coreTypes := []
  coreModules := []
  coreInstances := []
  funcs := []
  values := []
  types := []
  instances := []
  components := []

instance : Inhabited (Frame E) := ⟨Frame.empty⟩

end Silmaril.Wasm.Component.Instantiate
