module

public import Silmaril.Proofs.Wasm.Models.V2Core.Behaviours

/-!
# Instantiation as an observation: 2.0 instantiation runs are Core instantiation runs

* `instObs P p (m, xas)`: the behaviours, read in Core values, of the configuration that 2.0
  instantiation of `m` against the imports `xas` returns in the point `p`. The segment
  initialisation and the start function run as part of that configuration;
* `coreInstObs P x (cm, cxas)`: the same for Core 3.0;
* **`instObs_sub`**: under `InstantiationBounds` (a well-formed store and **no defined
  globals**), with a Core image of the store and the module, 2.0 instantiation observations are
  Core instantiation observations of the image.

This is the copied `instantiate_sim` (`Silmaril/Raw/Wasm/Versions/V2/ToCore/Instantiation.lean`)
followed by `behavioursOf_sub`. The `noGlobals` field is a real limitation of that proof, not a
missing argument. Core 3.0's `$evalglobals` allocates a temporary global instance per
initialiser, and `$allocmodule` then allocates the globals a second time. So with `n > 0`
defined globals, the Core store has `n` extra global instances and every global address is
shifted. Neither the store agreement nor `ModuleInstSim` can then hold. Lifting it needs a
simulation relation that is up to a renaming of global addresses.

New proofs over the copied simulation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2Core

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- 2.0 instantiation observations: the behaviours of an instantiation configuration. -/
def instObs (P : Profile) (p : Pt H)
    (mx : Silmaril.Wasm.V2.Module × List Silmaril.Wasm.V2.Execution.ExternAddr) :
    Set (Behaviour CVal) :=
  {b | ∃ c, Silmaril.Wasm.V2.Execution.Instantiate P p.2 p.1 mx.1 mx.2 c ∧
    b ∈ Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
      (Silmaril.Wasm.V2.Execution.behavioursOf P p.2 c)}

/-- Core 3.0 instantiation observations. -/
def coreInstObs (P : Profile) (x : Silmaril.Wasm.Atlas.Core.Pt H)
    (mx : Silmaril.Wasm.Module × List Silmaril.Wasm.Execution.Core.ExternAddr) :
    Set (Behaviour CVal) :=
  {b | ∃ C, Silmaril.Wasm.Execution.Core.Instantiate P x.2 x.1 mx.1 mx.2 C ∧
    b ∈ Silmaril.Wasm.Execution.Core.behavioursOf P x.2 C}

/-- **One 2.0 instantiation run is a Core instantiation run**, with included behaviours. -/
theorem instantiate_behaviours_sub (P : Profile) {s : VStore H} {src : VHost H}
    {X : CStore H} {m : Silmaril.Wasm.V2.Module} {cm : Silmaril.Wasm.Module}
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config H}
    (bounds : Silmaril.Wasm.V2.Execution.InstantiationBounds s m)
    (hX : Silmaril.Wasm.V2.Execution.Store.toCore s = some X)
    (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (hp : Silmaril.Wasm.V2.Execution.HostPreserves src) (hk : HostKeepsV src)
    (h : Silmaril.Wasm.V2.Execution.Instantiate P src s m xas c) :
    ∃ C, Silmaril.Wasm.Execution.Core.Instantiate P (liftHost src) X cm
        (xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) C ∧
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
          (Silmaril.Wasm.V2.Execution.behavioursOf P src c) ⊆
        Silmaril.Wasm.Execution.Core.behavioursOf P (liftHost src) C := by
  obtain ⟨C, hC, hsim, -⟩ :=
    Silmaril.Wasm.V2.Execution.instantiate_sim (tgt := liftHost src) bounds hX hcm h
  exact ⟨C, hC, behavioursOf_sub (compatible hp hk) hsim⟩

/-- **2.0 instantiation observations are Core instantiation observations** of the image. -/
theorem instObs_sub (P : Profile) {p : Pt H} (hp : dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Silmaril.Wasm.Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    (hg : m.globals = []) (xas : List Silmaril.Wasm.V2.Execution.ExternAddr) :
    instObs P p (m, xas) ⊆
      coreInstObs P (ptCore p) (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hp.2.1
  have hpt : ptCore p = (X, liftHost p.2) := by simp [ptCore, hX]
  rintro b ⟨c, hc, hb⟩
  obtain ⟨C, hC, hsub⟩ :=
    instantiate_behaviours_sub P ⟨hp.1, hg⟩ hX hcm hp.2.2.1 hp.2.2.2 hc
  rw [hpt]
  exact ⟨C, hC, hsub hb⟩

end Silmaril.Proofs.Wasm.Models.V2Core
