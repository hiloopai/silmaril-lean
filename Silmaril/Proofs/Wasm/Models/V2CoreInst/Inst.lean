module

public import Silmaril.Wasm.Models.V2Core.Thms
public import Silmaril.Wasm.Versions.Once.Thms

/-!
# Instantiation observations with defined globals

* `coreInstObsOnce P x (cm, cxas)`: the behaviours of the configuration that Core 3.0
  single-allocation instantiation (`CoreInstantiateOnce`, the relational `instantiateOnce?`)
  returns;
* `coreInstObsOnce_of_nil`: on a module without globals these are the spec's instantiation
  observations `coreInstObs`;
* **`instObs_sub_once`**: with a Core image of the module, 2.0 instantiation observations are
  Core single-allocation instantiation observations of the image, **for every module**, defined
  globals included (`instantiate_sim_once`, then `behavioursOf_sub`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInst

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Proofs.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- Core 3.0 single-allocation instantiation observations. -/
def coreInstObsOnce (P : Profile) (x : Silmaril.Wasm.Atlas.Core.Pt H)
    (mx : Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr) :
    Set (Behaviour CVal) :=
  {b | ∃ C, Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P x.2 x.1 mx.1 mx.2 C ∧
    b ∈ Silmaril.Wasm.Execution.Core.behavioursOf P x.2 C}

/-- On a module without globals, single allocation observes what the spec observes. -/
theorem coreInstObsOnce_of_nil (P : Profile) (x : Silmaril.Wasm.Atlas.Core.Pt H)
    {cm : Silmaril.Wasm.Module} (hg : cm.globals = [])
    (cxas : List Silmaril.Wasm.Execution.Core.ExternAddr) :
    coreInstObsOnce P x (cm, cxas) = coreInstObs P x (cm, cxas) := by
  ext b
  simp only [coreInstObsOnce, coreInstObs, Set.mem_ofPred_eq,
    Silmaril.Wasm.V2.Execution.Once.coreInstantiateOnce_of_nil hg]

/-- **One 2.0 instantiation run is a Core single-allocation instantiation run**, with included
behaviours, for every module with a Core image. -/
theorem instantiate_behaviours_sub_once (P : Profile) {s : VStore H} {src : VHost H}
    {X : CStore H} {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config H}
    (hwf : Silmaril.Wasm.V2.Execution.StoreWF s)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src)
    (h : Silmaril.Wasm.V2.Execution.Instantiate P src s m xas c) :
    ∃ C, Silmaril.Wasm.V2.Execution.Once.CoreInstantiateOnce P (liftHost src) X cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C ∧
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
          (Silmaril.Wasm.V2.Execution.behavioursOf P src c) ⊆
        Silmaril.Wasm.Execution.Core.behavioursOf P (liftHost src) C := by
  obtain ⟨C, hC, hsim, -⟩ :=
    Silmaril.Wasm.V2.Execution.Once.instantiate_sim_once (tgt := liftHost src) hwf hX hcm h
  exact ⟨C, hC, behavioursOf_sub (compatible hp hk) hsim⟩

/-- **2.0 instantiation observations are Core single-allocation instantiation observations**
of the image, with no restriction on the module's globals. -/
theorem instObs_sub_once (P : Profile) {p : Pt H} (hp : dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Silmaril.Wasm.Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (xas : List Silmaril.Wasm.V2.Execution.ExternAddr) :
    instObs P p (m, xas) ⊆
      coreInstObsOnce P (ptCore p) (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  have hpt : ptCore p = (X, liftHost p.2) := by simp [ptCore, hX]
  rintro b ⟨c, hc, hb⟩
  obtain ⟨C, hC, hsub⟩ :=
    instantiate_behaviours_sub_once P hp.1 hX hcm hp.2.2.1 hp.2.2.2 hc
  rw [hpt]
  exact ⟨C, hC, hsub hb⟩

end Silmaril.Proofs.Wasm.Models.V2CoreInst
