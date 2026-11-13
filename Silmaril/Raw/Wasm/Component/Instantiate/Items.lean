module

public import Silmaril.Wasm.Component.Reference.Instantiate.Items.Defs

public import Silmaril.Raw.Wasm.Component.Runtime.Ids
public import Silmaril.Raw.Wasm.Component.Types.Basic
public import Silmaril.Raw.Wasm.Component.Value.Basic
public import Silmaril.Raw.Wasm.Component.Validation.Context
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

variable {E : CoreEngine}

end Silmaril.Wasm.Component.Instantiate
