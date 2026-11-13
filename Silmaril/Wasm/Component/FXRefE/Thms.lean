module

public import Silmaril.Wasm.Component.FXRef.Thms
import Silmaril.Proofs.Wasm.Component.FXRefE.Facts

/-!
# The machine half over the WasmFX engine: discharged

`FXRef.RefToSpecEFXAll` asks that, at every profile `P`, every behaviour of the reference
component machine running `c.toRef` over the WasmFX engine `fxE P` be an outcome of the FX
engine's own canonical-ABI specification `exportSpecE (fxE P) ofNum`, for the components of
`Reference.refToSpec_of_arity`'s fragment. It is proved here, through the engine-generic
re-run of `refToSpec_of_arity` (`EngineRef.refToSpecEOn_of_facts`, also used for Lime1 by
`Lime1RefE`) from the engine facts of `fxE P`:

* **instantiation facts**: the FX engine prepares a Core module (no FX functions) at the
  machine's host type exactly as Core 3.0 does (`instantiateOnce?`), with no imports and the
  Core exports found by name;
* **run facts**: on that store (no host and no FX functions) a Core thread of the FX engine
  never calls an FX function or a host function (Core 3.0 `run_no_callout` on the renamed run),
  so its FX steps are Core 3.0 steps; returned values are typed (`run_results_typed`), and
  returned, trapping and diverging runs are runs of the `core3P P` engine instance, whose
  outcomes are those of `exportSpecE (fxE P) ofNum` (`FXEngine.exportSpecE_ofNum`).

Results (all proved, no hypotheses):

* `refToSpecE_fx : FXRef.RefToSpecEFXAll`;
* `refToSpec_fx : FXRef.RefToSpecFXAll` (with the engine-run half `FXRef.specSub_fx`);
* `Simple.sound_fxE'`: **soundness of the IR for the reference machine over the WasmFX
  engine**: every behaviour of a simple component of the fragment run by the reference machine
  over `fxE P` is matched by its IR denotation over `modSem P`;
* `Simple.sound_fxE_fxG'`: the same over the WasmFX game engine `fxG P`, under the per-module
  bridge hypothesis of `FXEngine.Simple.sound_fxG`.

Proofs in `Silmaril.Proofs.Wasm.Component.FXRefE.{Run,Facts}`. New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRefE

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXRef
open Silmaril.Wasm.Numerics (Profile)

/-- **The machine half over the WasmFX engine.** -/
theorem refToSpecE_fx : RefToSpecEFXAll :=
  Silmaril.Proofs.Wasm.Component.FXRefE.refToSpecE_fx

/-- **The reference-machine half over the WasmFX engine.** -/
theorem refToSpec_fx : RefToSpecFXAll :=
  refToSpec_fx_of refToSpecE_fx

/-- **Soundness of the IR for the reference machine over the WasmFX engine** (unconditional). -/
theorem Simple.sound_fxE' (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map ofCoreFX) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  FXRef.Simple.sound_fxE refToSpec_fx P prof c hc hf hi ha j vs hvs b hb

/-- **Soundness over the WasmFX game engine for the reference machine over the WasmFX engine**,
under the per-module bridge hypothesis of `Simple.sound_fxG` only. -/
theorem Simple.sound_fxE_fxG' (P : Profile)
    (hB : ∀ m : NumModule, (∃ I, m.IsInst I ∧ SameInst P m I) ∨
      (instOf (core3P P) m.mod [] m.exports = none ∧ ¬ ∃ I, m.IsInst I))
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxE P)) () (c.toRef.map ofCoreFX) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (fxG P).sem)
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  FXRef.Simple.sound_fxE_fxG refToSpec_fx P hB prof c hc hf hi ha j vs hvs b hb

end Silmaril.Wasm.Component.FXRefE
