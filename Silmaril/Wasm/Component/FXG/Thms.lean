module

public import Silmaril.Wasm.Component.FXG.Defs
public import Silmaril.Wasm.Models.FX.Thms
public import Silmaril.Wasm.Component.Hered.Thms
public import Silmaril.Wasm.Component.Core3G.Thms

/-!
# A WasmFX component engine over Core threads: theorems

* `ofCore_injective`: the FX image of Core configurations is injective;
* **`internalFX_iff`**: the WasmFX internal step on Core threads is the Core 3.0 internal step
  `InternalP P` (from `FX.stepFX_conservative` and `FX.blockFX_noFX`);
* **`fxE_eq`**: so the WasmFX engine over Core threads is the Core 3.0 engine, and
  `fxG P : GameEngine` is lawful with the game semantics of `core3G P` (`fxG_sem`);
* `refToSpecH_fxE` (and siblings): its hereditary soundness properties, hence
  **`Simple.sound_fxE`** and **`Linked2.sound_fxE`**: soundness of the reference component
  machine over the WasmFX engine against the IR.

This is the only WasmFX component instance the current definitions express: FX code cannot reach
a component (no FX module syntax), so every component run is a Core 3.0 run. An engine with FX
threads remains open (see `FXG.Defs`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXG

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
  Silmaril.Wasm.Component.Hered
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem ofCore_injective {H : Type} {c c' : Config H}
    (h : Silmaril.Wasm.Models.FX.ofCore c = Silmaril.Wasm.Models.FX.ofCore c') : c = c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', code'⟩ := c'
  simp only [Silmaril.Wasm.Models.FX.ofCore, Silmaril.Wasm.Models.FX.ConfigFX.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hc⟩ := h
  have hinj : Function.Injective Silmaril.Wasm.Models.FX.AdminFX.core := fun _ _ e => by cases e; rfl
  rw [List.map_inj_right hinj] at hc
  rw [hc]

/-- **The WasmFX internal step on Core threads is the Core 3.0 internal step.** -/
theorem internalFX_iff (P : Profile) {H : Type}
    {x y : Store H × Silmaril.Wasm.SingleThreaded.Thread} :
    InternalFX P x y ↔ Silmaril.Wasm.Game.InternalP P x y := by
  have hno : ∀ c : Config H, Silmaril.Wasm.Models.FX.NoFX Silmaril.Wasm.Models.FX.noFX c.store :=
    fun _ _ _ _ _ _ => rfl
  unfold InternalFX Silmaril.Wasm.Game.InternalP
  refine exists_congr fun f' => exists_congr fun code' => and_congr_right fun _ => ?_
  rw [Silmaril.Wasm.Models.FX.stepFX_conservative (hno _), Silmaril.Wasm.Models.FX.blockFX_noFX]
  exact ⟨fun ⟨_, hs, he⟩ => ofCore_injective he ▸ hs, fun hs => ⟨_, hs, rfl⟩⟩

theorem internalFX_eq (P : Profile) :
    (@InternalFX P) = @Silmaril.Wasm.Component.Engine.CoreEngine.Internal (core3P P) := by
  funext H x y
  exact propext (internalFX_iff P)

/-- **The WasmFX engine over Core threads is the Core 3.0 engine.** -/
theorem fxE_eq (P : Profile) : fxE P = core3P P := by
  unfold fxE
  rw [internalFX_eq P]

instance fxE_lawful (P : Profile) : (fxE P).Lawful := by
  rw [fxE_eq P]
  exact core3P_lawful P

/-- **The WasmFX engine over Core threads as a game engine.** -/
noncomputable def fxG (P : Profile) : GameEngine where
  E := fxE P
  lawful := fxE_lawful P
  abi := AbiLawful.ofLawful _
  M := NumModule
  core := inferInstance
  emb := NumModule.mod

/-- **The game semantics of the WasmFX engine is that of Core 3.0.** -/
theorem fxG_sem (P : Profile) : (fxG P).sem = (core3G P).sem := by
  show engineSem (Hered.withRel (core3P P) (core3P P).Valid (InternalFX P)) NumModule
    NumModule.mod = engineSem (core3P P) NumModule NumModule.mod
  rw [internalFX_eq P]

/-! ## Soundness -/

theorem subRel_fxE (P : Profile) : SubRel (core3P P) (InternalFX P) :=
  fun h => (internalFX_iff P).mp h

theorem refToSpecH_fxE (P : Profile) : RefToSpecH (fxE P) id P :=
  (refToSpecH_core3P P).withRel (subRel_fxE P)

theorem seqRefToSpecH_fxE (P : Profile) : SeqRefToSpecH (fxE P) id P :=
  (seqRefToSpecH_core3P P).withRel (subRel_fxE P)

theorem link2SoundH_fxE (P : Profile) : Link2SoundH (fxE P) id P :=
  (link2SoundH_core3P P).withRel (subRel_fxE P)

theorem link2SoundSeqH_fxE (P : Profile) : Link2SoundSeqH (fxE P) id P :=
  (link2SoundSeqH_core3P P).withRel (subRel_fxE P)

/-- **Soundness of the IR for the reference machine over the WasmFX engine.** -/
theorem Simple.sound_fxE (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map id) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.soundE (refToSpecH_fxE P).refToSpec prof c hc hf hi
    ha j vs hvs b hb

/-- **Soundness of two linked components over the WasmFX engine.** -/
theorem Linked2.sound_fxE (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (l : Linked2) (hEg : l.exp.Good) (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst)
    (har : l.imp.Arity) (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk)
    (hn : l.WireNodup) (hS : l.SplitOk) {σ : Type}
    (impl : Silmaril.Wasm.Component.Canon.HostImpl (fxE P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (linkHostE impl) h₀ (l.toRef.map id) []
      l.imp.exports[j].name (vs.map toRefVal)) :
    Reference.Linked2.IRObs P l j vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Linked2.soundE (link2SoundH_fxE P).link2Sound prof l hEg hEi
    hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

end Silmaril.Wasm.Component.FXG
