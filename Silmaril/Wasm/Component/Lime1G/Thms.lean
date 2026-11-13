module

public import Silmaril.Wasm.Component.Lime1G.Defs
public import Silmaril.Wasm.Component.Core3G.Thms

/-!
# Component instances for Lime1: theorems

* `lime1Emb_toCore`: the Lime1 engine runs the Core image of a Lime1 module as that module;
  `lime1G_sem_toCore`: so the game semantics of the IR module `⟨m.toCore, exps⟩` under `lime1G`
  is the engine strategy of the Lime1 instance of `m` itself;
* `core3LG_le`: Core 3.0 restricted to `lime1` refines the Core 3.0 game engine
  (`engineSem_restrict_le`), and `core3LG_le_modSem`: on a module whose Core 3.0 instance is
  the scalar instance of the IR, it refines `modSem P`;
* **`Simple.sound_core3LG`**, **`Linked2.sound_core3LG`**: soundness of the reference component
  machine over Core 3.0 restricted to `lime1` against the IR (simple components, and two linked
  components), instances of the I4/I5 restriction theorems.

Not proved here: soundness of the reference machine over `lime1G` itself. The reference-machine
half `RefToSpec` is proved by symbolic execution of `core3P P`; for `lime1G` it would need the
copied Lime1 → Core simulation lifted to the engine's callout view (`Engine.Lime1.steps_bridge`
gives the Lime1 machine side), which is not done.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Lime1G

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- The Lime1 engine runs the Core image of a Lime1 module as that module. -/
theorem lime1Emb_toCore (m : Silmaril.Wasm.Lime1.Module) (exps : CoreIface) :
    lime1Emb ⟨Silmaril.Wasm.Lime1.Module.toCore m, exps⟩ = m := by
  simp [lime1Emb]

theorem lime1G_sem : lime1G.sem = engineSem lime1G.E NumModule lime1G.emb := rfl

/-- **The Lime1 game semantics of the Core image of a Lime1 module** is that of the module
itself: the IR module `⟨m.toCore, exps⟩` denotes the engine strategy of the Lime1 instance of
`m`. -/
theorem lime1G_sem_toCore (m : Silmaril.Wasm.Lime1.Module) (exps : CoreIface) :
    lime1G.sem.sem ⟨Silmaril.Wasm.Lime1.Module.toCore m, exps⟩ =
      (engineSem lime1G.E NumModule (fun _ => m)).sem
        ⟨Silmaril.Wasm.Lime1.Module.toCore m, exps⟩ := by
  have he : lime1G.emb ⟨Silmaril.Wasm.Lime1.Module.toCore m, exps⟩ = m := lime1Emb_toCore m exps
  show (engineSem lime1G.E NumModule lime1G.emb).sem _ = _
  simp only [engineSem]
  rw [he]

/-- **Core 3.0 restricted to `lime1` refines Core 3.0.** -/
theorem core3LG_le (P : Profile) : (core3LG P).sem.Le (core3G P).sem :=
  engineSem_restrict_le (E := core3P P) (r := lime1R P) NumModule NumModule.mod

/-- On a module whose Core 3.0 instance is the IR's scalar instance, Core 3.0 restricted to
`lime1` refines `modSem P`. -/
theorem core3LG_le_modSem (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hS : SameInst P m I) :
    (core3LG P).sem.sem m ≤ (modSem P).sem m :=
  restrict_le_modSem P (lime1R P) hI hS

/-- **Soundness of the IR for the reference machine over Core 3.0 restricted to `lime1`.** -/
theorem Simple.sound_core3LG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (restrict (core3P P) (lime1R P))) () (c.toRef.map id) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Param.Simple.sound_restrict_core3P P (lime1R P) prof c hc hf hi ha j vs hvs b hb

/-- **Soundness of two linked components over Core 3.0 restricted to `lime1`.** -/
theorem Linked2.sound_core3LG (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (restrict (core3P P) (lime1R P)) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map id) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Reference.Linked2.IRObs P l j vs b :=
  Param.Linked2.sound_restrict_core3P P (lime1R P) prof l hEg hEi hIg hIi har hff hW hN hn hS
    impl h₀ j vs hvs b hb

end Silmaril.Wasm.Component.Lime1G
