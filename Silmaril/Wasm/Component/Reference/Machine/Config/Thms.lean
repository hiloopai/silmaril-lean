module

public import Silmaril.Wasm.Component.Reference.Machine.Config.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Machine.Config`: laws of the component reference

Theorems of the component reference copy `Machine.Config`, refined out of `Silmaril.Raw`: the
ones other topics use (through `Silmaril.Wasm.Component.Reference.Laws.Thms`) and the laws their
proofs need. The other theorems stay in `Silmaril.Raw.Wasm.Component.Machine.Config`, which
imports this module.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable (E : CoreEngine) (σ : Type)
variable {E σ}

namespace Config

theorem getElem?_setSlot_ne {α : Type} (xs : List (Option α)) (i j : Nat) (v : Option α)
    (h : j ≠ i) : ((setSlot xs i v)[j]?).join = (xs[j]?).join := by
  induction xs, i, v using setSlot.induct generalizing j <;> cases j <;> simp_all [setSlot]

theorem cont?_setCont_ne (m : Config E σ) (t u : ThreadId) (a : Option (Activation E σ))
    (h : u ≠ t) : (m.setCont t a).cont? u = m.cont? u :=
  getElem?_setSlot_ne _ _ _ _ fun e => h (by cases u; cases t; simp_all)

end Config

end Silmaril.Wasm.Component.Machine
