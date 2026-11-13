module

public import Silmaril.Wasm.Models.V2CoreInstDet.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff

/-!
# The reverse instantiation inclusion at the deterministic profile

* `instantiate_det`: the spec's `$instantiate` is deterministic, and its configuration depends
  neither on the profile nor on the host (`prepare?_iff`);
* `behavioursOf_of_closed`: a closed-host 2.0 behaviour of a configuration is a behaviour under
  every host;
* **`coreInstObs_sub_det`**: at `Profile.deterministic g`, at a point of `v20instHT`'s domain,
  take a 2.0 instantiation run `c` of a module with a Core image whose closed-host behaviours
  are not empty. Then the spec observations of the image call lie inside the mapped 2.0
  behaviours of `c`. This is the call model's `behaviours_det_eq` argument at the instantiation
  configuration. The copied `instantiate_sim_once` relates `c` to a single-allocation image `C`.
  The closed-host behaviour of `c` is a closed-host behaviour of `C`, so by `DetLift` it is
  `C`'s only behaviour under every host. `once_eq_spec_hostR` and `instantiate_det` give the
  spec run the same behaviours as `C`.
* `instObs_eq_det`: so on such calls the spec observations are the 2.0 instantiation
  observations.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstDet

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
  Silmaril.Proofs.Wasm.Models.V2Core
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

/-- **The spec's `$instantiate` is deterministic**, across profiles and hosts. -/
theorem instantiate_det {P P' : Profile} {host host' : HostSemantics H} {s : Store H}
    {m : Module} {xas : List ExternAddr} {c c' : Config H} (hc : Instantiate P host s m xas c)
    (hc' : Instantiate P' host' s m xas c') : c = c' := by
  have e₁ := (prepare?_iff (P := P) (host := host) hc.valid).mpr hc
  have e₂ := (prepare?_iff (P := P') (host := host') hc.valid).mpr hc'
  exact Option.some.inj (e₁.symm.trans e₂)

/-- A closed-host 2.0 behaviour of a configuration is a behaviour under every host. -/
theorem behavioursOf_of_closed {P : Profile} {src : VHost H}
    {c : Silmaril.Wasm.V2.Execution.Config H} :
    Silmaril.Wasm.V2.Execution.behavioursOf P closedV c ⊆
      Silmaril.Wasm.V2.Execution.behavioursOf P src c := by
  rintro b (⟨c', r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨c', r, steps_of_closed hrun, hcode, rfl⟩
  · exact Or.inr ⟨rfl, diverges_of_closed hdiv⟩

/-- **Spec observations of an image call lie inside the mapped 2.0 behaviours** of a 2.0
instantiation run with a closed-host behaviour, at the deterministic profile. -/
theorem coreInstObs_sub_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : (v20instHT (Profile.deterministic g)).dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c)
    (htot : (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV
      c).Nonempty) :
    coreInstObs (Profile.deterministic g) (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) ⊆
      Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
        (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) p.2 c) := by
  obtain ⟨hd, hv, hs⟩ := hp
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hd.2.1
  have hpt : ptCore p = (X, liftHost p.2) := by simp [ptCore, hX]
  -- the single-allocation image `C` of `c`
  obtain ⟨C, hC, hsim, -⟩ :=
    Silmaril.Wasm.V2.Execution.Once.instantiate_sim_once (tgt := liftHost p.2) hd.1 hX hcm hc
  -- the closed-host behaviour `b₀` of `c` is a closed-host behaviour of `C`
  obtain ⟨b₀, hb₀⟩ := htot
  have hsubC : Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
      (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV c) ⊆
      behavioursOf (Profile.deterministic g) (liftHost closedV) C :=
    behavioursOf_sub (compatible closedV_preserves closedV_keeps) hsim
  have hb₀C : Behaviour.map Silmaril.Wasm.V2.Execution.Val.toCore b₀ ∈
      behavioursOf (Profile.deterministic g) Silmaril.Wasm.Binaryen.closedHost C :=
    liftHost_closed ▸ hsubC ⟨b₀, hb₀, rfl⟩
  -- the spec run `C'` has the behaviours of `C`
  have hsX : GlobalsNamed X := by simpa only [hpt] using hs
  have hvalid : Silmaril.Wasm.V2.Validation.ModuleValid m :=
    let ⟨ixt, xt, hok, _⟩ := hc.valid; ⟨ixt, xt, hok⟩
  obtain ⟨C', hC', hbeh⟩ := Silmaril.Wasm.Models.V2CoreSpecImg.once_eq_spec_hostR
    (hostEmbR_liftHost hv) hsX
    (fun c' st' hc' => Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg_of_toCore hX m cm _ c' st'
      hvalid hcm hc') hC
  -- so every spec observation is `b₀`, read in Core values
  show coreInstObs (Profile.deterministic g) (ptCore p) _ ⊆ _
  rw [hpt]
  rintro b ⟨D, hD, hb⟩
  have hDC : D = C' := instantiate_det hD hC'
  have hbC : b ∈ behavioursOf (Profile.deterministic g) (liftHost p.2) C := by
    rw [← hbeh, ← hDC]; exact hb
  have hb_eq : b = Behaviour.map Silmaril.Wasm.V2.Execution.Val.toCore b₀ :=
    core_behaviours_sub_singleton hb₀C (liftHost p.2) hbC
  exact ⟨b₀, behavioursOf_of_closed hb₀, hb_eq.symm⟩

/-- **On such calls the spec observations are the 2.0 instantiation observations.** -/
theorem instObs_eq_det (g : GrowKind → Nat → Nat → Nat → Bool) {p : Pt Nat}
    (hp : (v20instHT (Profile.deterministic g)).dom p) {m : Silmaril.Wasm.V2.Module}
    {cm : Module} (hcm : Silmaril.Wasm.V2.Module.toCore m = some cm)
    {xas : List Silmaril.Wasm.V2.Execution.ExternAddr}
    {c : Silmaril.Wasm.V2.Execution.Config Nat}
    (hc : Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) p.2 p.1 m xas c)
    (htot : (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) closedV
      c).Nonempty) :
    coreInstObs (Profile.deterministic g) (ptCore p)
        (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) =
      instObs (Profile.deterministic g) p (m, xas) := by
  refine Set.Subset.antisymm (fun b hb => ⟨c, hc, coreInstObs_sub_det g hp hcm hc htot hb⟩) ?_
  intro b hb
  have hsome : (Silmaril.Wasm.V2.Module.toCore m).isSome := by rw [hcm]; rfl
  have h := inst_obs_sub_spec_H (Profile.deterministic g) hp.1 hp.2.1 hp.2.2
    (Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg p hp.1) (m, xas) ⟨hsome, hb⟩
  have e : instCall (m, xas) = (cm, xas.map Silmaril.Wasm.V2.Execution.ExternAddr.toCore) := by
    simp [instCall, modCore, hcm]
  rw [e] at h
  exact h

end Silmaril.Proofs.Wasm.Models.V2CoreInstDet
