module

public import Silmaril.Wasm.Component.FXRef.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms
public import Silmaril.Wasm.Component.Param.Thms
public import Silmaril.Wasm.Component.Lime1Ref.Thms
import Silmaril.Proofs.Wasm.Component.FXRef.Spec

/-!
# The reference-machine half over the WasmFX engine: conditional results

* `ofNum_eq`: `ofNum m` is `ofCoreFX m.mod`;
* `refToSpecOn_fx_of`: the same reduction as for Lime1 (`refToSpecOn_of_specE`): on any domain,
  the machine half against the FX engine's own specification and the engine-run half give the
  reference-machine half over `fxE P`;
* `specSub_core3P`: **the engine-run half for Core 3.0**: for every `Simple.Inst` component the
  canonical-ABI specification over `core3P P` is contained in `exportSpec P` (the engine instance
  of the module is its `IsInst` instance up to the host type, and engine runs are Core runs);
* `specSub_fx`: **the engine-run half for WasmFX**, `SpecSubOn (fxE P) ofNum P` on every
  component, from `exportSpecE_ofNum` (the FX specification is the Core 3.0 one on numeric
  modules) and `specSub_core3P`;
* `refToSpecOn_fx_of_E`, `refToSpec_fx_of`: so the reference-machine half over `fxE P` follows
  from its machine half alone: `RefToSpecEFXAll → RefToSpecFXAll`;
* `Simple.sound_fxE`: **assuming `RefToSpecFXAll`** (`Simple.sound_fxE_of`: assuming only
  `RefToSpecEFXAll`), every behaviour of the reference machine
  running a simple component over the FX engine is matched by its IR denotation over
  `modSem P`, and (`Simple.sound_fxE_fxG`) over the WasmFX game engine `fxG P` under the per-module
  bridge hypothesis of `Simple.sound_fxG`.

New statements; `RefToSpecFXAll` and `RefToSpecEFXAll` are open.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.Lime1Ref
open Silmaril.Wasm.Numerics (Profile)

theorem ofNum_eq (m : NumModule) : ofNum m = ofCoreFX m.mod := rfl

/-- **The reduction of the FX half to two halves** (as for Lime1). -/
theorem refToSpecOn_fx_of {P : Profile} {D : Simple → Prop}
    (hR : RefToSpecEOn (fxE P) ofCoreFX ofNum D) (hS : SpecSubOn (fxE P) ofNum P D) :
    RefToSpecOn (fxE P) ofCoreFX P D :=
  refToSpecOn_of_specE hR hS

/-- **The engine-run half for Core 3.0**: for a component whose module is instantiated as the IR
assumes, every outcome of the canonical-ABI specification over `core3P P` is one of `exportSpec P`. -/
theorem specSub_core3P (P : Profile) : SpecSubOn (core3P P) NumModule.mod P fun _ => True :=
  Silmaril.Proofs.Wasm.Component.FXRef.specSub_core3P

/-- **The engine-run half for WasmFX** (on every component). -/
theorem specSub_fx (P : Profile) : SpecSubOn (fxE P) ofNum P fun _ => True := by
  intro c hD hc hi x hx vs
  rw [exportSpecE_ofNum]
  exact specSub_core3P P c hD hc hi x hx vs

/-- **The reference-machine half over the WasmFX engine from its machine half**, on any domain. -/
theorem refToSpecOn_fx_of_E {P : Profile} {D : Simple → Prop}
    (hR : RefToSpecEOn (fxE P) ofCoreFX ofNum D) : RefToSpecOn (fxE P) ofCoreFX P D :=
  refToSpecOn_fx_of hR fun c _ hc hi => specSub_fx P c trivial hc hi

/-- **`RefToSpecFXAll` follows from the machine half `RefToSpecEFXAll`.** -/
theorem refToSpec_fx_of (hR : RefToSpecEFXAll) : RefToSpecFXAll := fun P =>
  fun prof c hc hf hi ha =>
    refToSpecOn_fx_of_E (D := fun _ => True) (fun prof c _ => hR P prof c) prof c trivial hc hf hi ha

/-- **Soundness of the IR for the reference machine over the WasmFX engine**, assuming the
reference-machine half `RefToSpecFXAll`. -/
theorem Simple.sound_fxE (hR : RefToSpecFXAll) (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map ofCoreFX) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.Simple.soundE (hR P) prof c hc hf hi ha j vs hvs b hb

/-- **Soundness of the IR for the reference machine over the WasmFX engine**, assuming only the
machine half `RefToSpecEFXAll`. -/
theorem Simple.sound_fxE_of (hR : RefToSpecEFXAll) (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map ofCoreFX) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Simple.sound_fxE (refToSpec_fx_of hR) P prof c hc hf hi ha j vs hvs b hb

/-- **Soundness over the WasmFX game engine for the reference machine over the WasmFX engine**,
assuming `RefToSpecFXAll` and the per-module bridge hypothesis of `Simple.sound_fxG`. -/
theorem Simple.sound_fxE_fxG (hR : RefToSpecFXAll) (P : Profile)
    (hB : ∀ m : NumModule, (∃ I, m.IsInst I ∧ SameInst P m I) ∨
      (instOf (core3P P) m.mod [] m.exports = none ∧ ¬ ∃ I, m.IsInst I))
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map ofCoreFX) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (fxG P).sem)
      ⟨j, by simp [Simple.toComp]⟩ vs b := by
  have hsem : (fxG P).sem = modSem P := CoreSem.ext' (funext fun m =>
    (congrArg (fun C : CoreSem NumModule => C.sem m) (fxG_sem_eq_core3G P)).trans
      (core3G_sem_eq_modSem_of P hB m))
  rw [hsem]
  exact Simple.sound_fxE hR P prof c hc hf hi ha j vs hvs b hb

end Silmaril.Wasm.Component.FXRef
