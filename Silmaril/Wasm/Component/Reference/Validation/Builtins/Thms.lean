module

public import Silmaril.Wasm.Component.Reference.Validation.Builtins.Defs
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Defs
public import Init.Data.String.Defs
public import Init.Data.Repr
public import Silmaril.Wasm.Component.Reference.Validation.CanonOpts.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Validation.ValTypes.Thms

/-!
# `Validation.Builtins`: laws of the component reference

Theorems of the component reference copy `Validation.Builtins`, refined out of
`Silmaril.Raw.Wasm.Component.Validation.Builtins`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Validation

open Silmaril.Wasm.Component.Types
variable {X : Type}

theorem checkBuiltin?_sound {feat : Features} {V : BuiltinView X} {Γ Γ' : Ctx X}
    {b : Syntax.Builtin} {x : X} (h : checkBuiltin? feat V Γ b = .ok (x, Γ')) :
    ValidBuiltin feat V Γ b x Γ' := by
  unfold checkBuiltin? at h
  split at h
  · split at h
    · cases h; exact .mk (by assumption)
    · cases h
  · cases h

end Silmaril.Wasm.Component.Validation
