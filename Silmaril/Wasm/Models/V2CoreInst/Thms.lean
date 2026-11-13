module

public import Silmaril.Proofs.Wasm.Models.V2CoreInst.Inst

/-!
# Instantiation observations of `v20own → core|v20` without `noGlobals`

`Silmaril.Wasm.Models.V2Core.v20InstEmb` observes a 2.0 module only when it has no defined globals
(`InstantiationBounds.noGlobals`), because Core 3.0's spec `$instantiate` allocates every global
twice (`$evalglobals`, then `$allocmodule`) and so shifts the module's global addresses.

This header states instantiation observations **for every module** against Core 3.0 with each
global allocated once, which is silmaril-lean's `instantiateOnce?` and the instantiation of the
component engine (`Silmaril.Wasm.Component.Engine.Core3.prepareE?`):

* `CoreInstantiateOnce` (in `Silmaril/Raw/Wasm/Versions/V2/ToCore/InstantiationOnce.lean`): the
  relational single-allocation instantiation; `coreInstantiateOnce_of_nil`: it is the spec's
  `$instantiate` on modules without globals;
* `instantiate_sim_once`: every 2.0 instantiation is simulated (`Sim`) by it, with no `noGlobals`;
  the 2.0 side is reduced to the global-free case by allocating the globals first
  (`allocModule?_dropGlobals`), and the constant-expression lemmas are restated for Core states
  that extend the 2.0 globals (`ConstAgree`);
* `v20instG P H`: the 2.0 instantiation model observing **every** module with a Core image;
  `coreInstOnce P H S`: the Core single-allocation instantiation model restricted to `S`;
* **`v20InstEmbG P H : (v20instG P H).Emb (coreInstOnce P H v20)`**, direction `sub`, with
  `v20InstTransG`;
* `coreInstOnce_obs_of_nil`: on modules without globals `coreInstOnce` observes what the spec's
  `coreInst` observes, so `v20InstEmbG` extends `v20InstEmb`.

**Why not the spec's `$instantiate`.** With defined globals, the spec's Core store holds `n` more
globals than the 2.0 store (unreachable `$evalglobals` copies). A host call made by the start
function or later sees that store; the induced host `liftHost src` answers on the 2.0 store with
those extra globals, about which the 2.0 host `src` is unconstrained. So inclusion into the spec's
observations needs hosts that are invariant under global-address embeddings, which the points of
`v20own` do not require. Single allocation is exactly the image, and is what the engine runs.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.V2CoreInst

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Atlas Silmaril.Wasm.Models.V2Core
  Silmaril.Proofs.Wasm.Models.V2CoreInst
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **The 2.0 instantiation model, every module**: a call (a module and its imports) is observed
whenever the module has a Core image. -/
def v20instG (P : Profile) (H : Type) : WasmModel where
  feats := Silmaril.Wasm.Models.v20
  Module := Silmaril.Wasm.V2.Module
  Valid := (v20own P H).Valid
  Pt := Pt H
  Call := Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr
  Obs := Behaviour CVal
  obs p mx := {b | (Silmaril.Wasm.V2.Module.toCore mx.1).isSome ∧
    b ∈ Silmaril.Proofs.Wasm.Models.V2Core.instObs P p mx}
  dom := dom

/-- **The Core single-allocation instantiation model** restricted to `S`. -/
def coreInstOnce (P : Profile) (H : Type) (S : FeatureSet) : WasmModel where
  feats := S
  Module := Silmaril.Wasm.Module
  Valid := ValidIn S
  Pt := Silmaril.Wasm.Atlas.Core.Pt H
  Call := Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr
  Obs := Behaviour CVal
  obs := coreInstObsOnce P
  dom := coreDom S

/-- **2.0 instantiation observations are Core single-allocation instantiation observations** of
the image, for every module. -/
theorem inst_obs_sub_once (P : Profile) {p : Pt H} (hp : dom p)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20instG P H).obs p mx ⊆ coreInstObsOnce P (ptCore p) (instCall mx) := by
  rintro b ⟨hsome, hb⟩
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp hsome
  have e : modCore mx.1 = cm := by simp [modCore, hcm]
  simp only [instCall, e]
  exact instObs_sub_once P hp hcm mx.2 hb

/-- **The instantiation embedding without `noGlobals`** `v20instG → coreInstOnce|v20`
(direction `sub`). -/
def v20InstEmbG (P : Profile) (H : Type) : (v20instG P H).Emb (coreInstOnce P H v20) where
  mod := modCore
  valid := (v20Emb P H).valid
  pt := ptCore
  call := instCall
  readback := some
  dom _ hp := ptCore_dom hp
  dir := .sub
  sat _ hp mx := fun b hb => ⟨b, inst_obs_sub_once P hp mx hb, rfl⟩

theorem v20InstEmbG_dir (P : Profile) (H : Type) : (v20InstEmbG P H).dir = .sub := rfl

/-- The atlas transition of the instantiation embedding without `noGlobals`. -/
def v20InstTransG (P : Profile) (H : Type) :
    Transition (v20instG P H).chart ((coreInstOnce P H v20).viewChart some) :=
  (v20InstEmbG P H).toTransition

/-- On modules without globals the single-allocation model observes what the spec's
instantiation model `coreInst` observes. -/
theorem coreInstOnce_obs_of_nil (P : Profile) (S : FeatureSet) (x : Silmaril.Wasm.Atlas.Core.Pt H)
    {cm : Silmaril.Wasm.Module} (hg : cm.globals = [])
    (cxas : List Silmaril.Wasm.Execution.Core.ExternAddr) :
    (coreInstOnce P H S).obs x (cm, cxas) = (coreInst P H S).obs x (cm, cxas) :=
  coreInstObsOnce_of_nil P x hg cxas

/-- `v20instG` observes at least what `v20inst` observes (it drops the `noGlobals` guard). -/
theorem v20inst_obs_sub (P : Profile) (p : Pt H)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    (v20inst P H).obs p mx ⊆ (v20instG P H).obs p mx :=
  fun _ hb => ⟨hb.2.1, hb.2.2⟩

/-! The axiom audit. -/

/--
info: 'Silmaril.Wasm.Models.V2CoreInst.v20InstEmbG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms v20InstEmbG

/--
info: 'Silmaril.Wasm.V2.Execution.Once.instantiate_sim_once' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.V2.Execution.Once.instantiate_sim_once

end Silmaril.Wasm.Models.V2CoreInst
