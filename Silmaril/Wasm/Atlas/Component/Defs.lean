module

public import Silmaril.Wasm.Atlas.Defs
public import Silmaril.Wasm.Component.Reference.LinkSound.Defs

/-!
# The component charts

Two charts for two linked components (`Silmaril.Wasm.Component.Reference.Linked2`), at a Core
profile `P`, a component choice profile `prof`, and host functions `impl` with initial host
state `h₀`. Calls are an export index of the importer with IR argument values; observations are
reference `Outcome`s. Both observation sets only contain outcomes of well-typed calls of
existing exports.

* `Component.refChart`: the reference Component Model machine over Core 3.0
  (`exportBehaviours` of `l.toRef` under `linkHost impl`). Domain: `Linked2.sound`'s fragment
  (`Component.Dom`).
* `Component.irChart`: the component IR (`l.toComp.den (impSem P)`), read through
  `Linked2.IRObs`: a returned outcome is observed when the IR has the play answering with values
  whose reference images are the results; a trap when the IR has the trap play; every other
  outcome (divergence, deadlock, cancellation) is not constrained by the IR and is always
  observed.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Component

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- `Linked2.sound`'s fragment. -/
def Dom (l : Linked2) : Prop :=
  l.exp.Good ∧ l.exp.Inst ∧ l.imp.Good ∧ l.imp.Inst ∧ l.imp.Arity ∧ l.imp.FloatFree ∧
    l.WireTy ∧ l.NamesOk ∧ l.WireNodup ∧ l.SplitOk

/-- Component calls: an export index of the importer and IR argument values. -/
abbrev Call : Type := Nat × List Silmaril.Wasm.Component.Val

/-- Reference observations of a well-typed call. -/
def refObs (prof : Silmaril.Wasm.Component.ProfileKind) {P : Profile} {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) (l : Linked2)
    (c : Call) : Set Outcome :=
  {b | ∃ h : c.1 < l.imp.exports.length,
    Silmaril.Wasm.Component.ValTy.checkList (l.imp.exports[c.1]'h).ty.params c.2 = true ∧
    b ∈ exportBehaviours prof (linkHost impl) h₀ l.toRef [] (l.imp.exports[c.1]'h).name
      (c.2.map toRefVal)}

/-- IR observations of a well-typed call (`Linked2.IRObs`). -/
def irObs (P : Profile) (l : Linked2) (c : Call) : Set Outcome :=
  {b | ∃ h : c.1 < l.imp.exports.length,
    Silmaril.Wasm.Component.ValTy.checkList (l.imp.exports[c.1]'h).ty.params c.2 = true ∧
    Linked2.IRObs P l ⟨c.1, h⟩ c.2 b}

/-- **The reference chart.** -/
def refChart (prof : Silmaril.Wasm.Component.ProfileKind) {P : Profile} {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ) : Chart :=
  BChart Linked2 Call Outcome Dom (refObs prof impl h₀)

/-- **The component IR chart.** -/
def irChart (P : Profile) : Chart :=
  BChart Linked2 Call Outcome Dom (irObs P)

end Silmaril.Wasm.Atlas.Component
