module

public import Silmaril.Wasm.Component.Reference.Canon.Callout.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms

/-!
# `Canon.Callout`: laws of the component reference

Theorems of the component reference copy `Canon.Callout`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Callout`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
variable {E : CoreEngine} {σ : Type}

/-- Every operation of `confine p` observes (the trap `cannotLeave` included). -/
theorem confine_every {α : Type} {Q : Op E σ → Prop} (hQ : ∀ o, Op.observes o = true → Q o)
    (p : P E σ α) : Prog.Every (S := Eff E σ) Q (confine p) := by
  induction p with
  | pure a => exact Prog.Every.pure a
  | op o k ih =>
    dsimp only [confine]
    split
    · exact Prog.Every.op (hQ o (by assumption)) ih
    · exact Prog.Every.op (hQ (.trap .cannotLeave) rfl) fun e => nomatch e

/-- An observing operation updates no store. -/
theorem Op.preservesInv_of_observes (I : CStore E → Prop) {o : Op E σ}
    (h : Op.observes o = true) : Op.PreservesInv I o := by
  cases o <;> trivial

/-- Confined code preserves every store invariant (it updates no store). -/
theorem P.Inv.confine (I : CStore E → Prop) {α : Type} (p : P E σ α) :
    P.Inv I (Canon.confine p) :=
  confine_every (fun _ h => Op.preservesInv_of_observes I h) p

end Silmaril.Wasm.Component.Canon
