module

public import Silmaril.Wasm.Component.Reference.Validation.Context.Defs
public import Silmaril.Wasm.Component.Reference.Features.Defs
public import Silmaril.Wasm.Component.Reference.Syntax.Basic.Defs
public import Silmaril.Wasm.Component.Reference.Types.Basic.Defs
public import Silmaril.Wasm.Validation.DefTypes
public import Init.Data.String.Defs
public import Init.Data.Repr

/-!
# `Validation.Context`: laws of the component reference

Theorems of the component reference copy `Validation.Context`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.Context`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types

namespace Ctx

variable {X : Type}

theorem listAt?_eq_ok {α : Type} {what space : String} {l : List α} {i : Nat} {a : α} :
    listAt? what space l i = .ok a ↔ l[i]? = some a := by
  unfold listAt?
  cases l[i]? <;> simp

end Ctx

end Silmaril.Wasm.Component.Validation
