module

public import Silmaril.Wasm.Component.FXRefV.Defs
public import Silmaril.Wasm.Component.FXEngineV.Thms
public import Silmaril.Wasm.Component.Param.Thms
import Silmaril.Proofs.Wasm.Component.FXRefV.Run

/-!
# The reference-machine half for components whose modules carry FX functions

`FXRefE.refToSpecE_fx` is the machine half over the WasmFX engine `fxE P` for Core modules seen
as FX modules (no FX functions). Here the components' modules carry FX functions
(`SimpleFX`: a Core module, FX function declarations, lifted exports of Core or FX functions),
and the engine is `fxEV P`, where FX functions are in the function index space of FX code and
threads run by `StepFX'`, so exported FX code can `suspend`, `resume`, `switch`, `cont.bind`
and `resume_throw`.

Results (proofs in `Silmaril.Proofs.Wasm.Component.FXRefV.{Map,Inst,Run}`):

* `refToSpecFX P : RefToSpecFX P`: for a component in the fragment of `refToSpec_of_arity`
  (`Good`, `FloatFree`, `Arity` of `c.toSimple`; `SimpleFX.Inst`) **whose engine runs return
  typed values** (`SimpleFX.Typed P c`), every behaviour of calling export `x` of the reference
  component, run by the reference component machine over `fxEV P` with the FX functions
  attached to the core module, is an outcome of the engine's own canonical-ABI specification
  `exportSpecE (fxEV P) c.emb c.toSimple x vs`;
* `SimpleFX.sound_fxEV`: hence **soundness of the IR over the suspending engine**: every such
  behaviour is matched by the IR denotation of `c.toSimple` over `engineSem (fxEV P) NumModule
  c.emb` (with `Param.specToIRE`).

The proof re-runs `refToSpec_of_arity` over `fxEV P` (`EngineRef.refToSpecE_of_facts`). The
instantiation facts hold because `fxEV P` instantiates the Core part as Core 3.0 and allocates
the FX functions after it, with distinct fresh export names. The run facts hold for every FX
code: the instantiated store has no component host functions, and engine steps keep the
function instances, so no reached thread is parked or at a callout; the machine's runs (host
type `CanonHost (fxEV P)`) rename to runs of the specification's instance (host type `Nat`),
with returned statuses kept (renaming is invertible on host-free stores). The only fact the
proof does not derive is the typing of returned values, which is `SimpleFX.Typed`: type
soundness of `StepFX'` runs at the export types. It is open for FX code (`TypedFX` types only
straight-line FX code and has no preservation theorem).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRefV

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Numerics (Profile)

/-- **The reference-machine half for components whose modules carry FX functions**, over the
WasmFX engine with suspension, for components whose engine runs return typed values. -/
theorem refToSpecFX (P : Profile) : RefToSpecFX P :=
  Silmaril.Proofs.Wasm.Component.FXRefV.refToSpecFX P

/-- **Soundness of the IR over the suspending WasmFX engine for components with FX
functions**: every behaviour of the reference machine over `fxEV P` is matched by the IR
denotation over the game semantics of `fxEV P`. -/
theorem SimpleFX.sound_fxEV (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : SimpleFX) (hc : c.toSimple.Good) (hf : c.toSimple.FloatFree) (hi : c.Inst)
    (ha : c.toSimple.Arity) (ht : c.Typed P) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHostE (fxEV P)) () (c.toSimple.toRef.map c.ofCore) []
      c.exports[j].name (vs.map toRefVal)) :
    IRObs (k := c.toSimple.toComp.exports.length)
      (c.toSimple.toComp.den (engineSem (fxEV P) NumModule c.emb))
      ⟨j, by simp [Simple.toComp, SimpleFX.toSimple]⟩ vs b :=
  Silmaril.Proofs.Wasm.Component.Param.specToIRE (E := fxEV P) c.emb c.toSimple hc j vs b
    (refToSpecFX P prof c hc hf hi ha ht _ (List.getElem_mem j.isLt) vs hvs hb)

/-- info: 'Silmaril.Wasm.Component.FXRefV.refToSpecFX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refToSpecFX

/--
info: 'Silmaril.Wasm.Component.FXRefV.SimpleFX.sound_fxEV' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SimpleFX.sound_fxEV

end Silmaril.Wasm.Component.FXRefV
