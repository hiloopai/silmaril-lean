module

public import Silmaril.Proofs.Wasm.Models.V2CoreInstHost.Run

/-!
# `liftHost` breaks the instantiation equality without a closed-host behaviour

The call model's `DetFalse` at an instantiation run. `ptX` and `pt` have the same Core image, so
the spec observations at `ptCore pt` include what the 2.0 run at `ptX` does (`inst_obs_sub_spec_H`
with `specGlobalsImg`). At `ptX` the start function's host call returns; at `pt` it only diverges.

* `core_returns`: the spec observations of `mI`'s image call at `ptCore pt` contain `returns []`;
* `obs_pt`: `v20instG` observes exactly `diverges` on `(mI, xasI)` at `pt`;
* **`instHost_not_eq`**: at every profile, `pt` is in `v20instHT`'s domain, `mI` is 2.0-valid
  with a Core image, and the spec observations of `instCallE (mI, xasI)` differ from `v20instG`'s;
* `not_domInstDet`: so `pt` is not in `domInstDet g` (by `obs_eq_det`);
* **`coreInstObs_not_sub`**: without the closed-host behaviour, `coreInstObs_sub_det`'s
  conclusion fails at `Profile.deterministic g`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstHost

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Proofs.Wasm.Models.V2Core
  Silmaril.Wasm.Models.V2CoreInst Silmaril.Wasm.Models.V2CoreSpec Silmaril.Wasm.Models.V2CoreInstDet
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.V2.Execution (Admin Config Step Steps vals Result)

/-- At `st`, `mI` instantiates to `cI st`. -/
theorem inst_st (P : Profile) :
    Silmaril.Wasm.V2.Execution.Instantiate P src st mI xasI (cI st) where
  valid := ⟨_, _, mI_ok, .cons (.func (fi := fiH) rfl) .nil⟩
  bounded := by simp [mI]
  run := ⟨[], [], st, miI, .nil, .nil, alloc_st, rfl⟩

/-- At `st`, the run diverges: the host call stutters. -/
theorem diverges_st (P : Profile) : Silmaril.Wasm.V2.Execution.Diverges P src (cI st) := by
  refine ⟨fun n => if n = 0 then cI st else cA st, rfl, fun n => ?_⟩
  have hA : Step P src (cA st) (cA st) :=
    .callAddrHostDiv (vs := []) (fi := fiH) (h := 0) rfl rfl rfl (Or.inl rfl)
  rcases n with _ | n
  · exact .read (.call (a := 0) rfl)
  · exact hA

theorem mI_some : (Silmaril.Wasm.V2.Module.toCore mI).isSome := rfl

/-- **`v20instG` observes exactly `diverges`** on `(mI, xasI)` at `pt`. -/
theorem obs_pt (P : Profile) : (v20instG P Nat).obs pt (mI, xasI) = {.diverges} := by
  ext b
  change _ ↔ b = .diverges
  constructor
  · rintro ⟨-, c, hc, b', hb', rfl⟩
    have e : c = cI st := inst_eq alloc_st hc
    subst e
    rw [behaviours_st P hb']
    rfl
  · rintro rfl
    exact ⟨mI_some, cI st, inst_st P, .diverges, Or.inr ⟨rfl, diverges_st P⟩, rfl⟩

/-- **The spec observations of `mI`'s image call at `ptCore pt` contain `returns []`.** -/
theorem core_returns (P : Profile) :
    Behaviour.returns [] ∈ coreInstObs P (ptCore pt) (instCall (mI, xasI)) := by
  have hd := ptX_dom P
  have hsub := inst_obs_sub_spec_H P hd.1 hd.2.1 hd.2.2
    (Silmaril.Wasm.Models.V2CoreSpecImg.specGlobalsImg ptX hd.1) (mI, xasI)
  have hb : Behaviour.returns [] ∈ (v20instG P Nat).obs ptX (mI, xasI) :=
    ⟨mI_some, cI stX, inst_stX P, .returns [], returns_stX P, rfl⟩
  have h := hsub hb
  rw [ptCore_ptX] at h
  exact h

theorem instCallE_mI : instCallE (mI, xasI) = instCall (mI, xasI) := by
  obtain ⟨cm, hcm⟩ := Option.isSome_iff_exists.mp mI_some
  unfold instCallE
  rw [hcm]
  dsimp only
  simp only [mI_valid, ↓reduceIte, instCall, modCore, hcm, Option.getD_some]

/-- **The instantiation equality fails through `liftHost`**, at every profile: at the point
`pt` of `v20instHT`'s domain, for the 2.0-valid module `mI` with a Core image, the spec
observations of `instCallE (mI, xasI)` contain `returns []`, and `v20instG` observes only
`diverges`. -/
theorem instHost_not_eq (P : Profile) :
    (v20instHT P).dom pt ∧ Silmaril.Wasm.V2.Validation.ModuleValid mI ∧
      (Silmaril.Wasm.V2.Module.toCore mI).isSome ∧
      Behaviour.returns [] ∈ (coreInst P Nat v20).view some (ptCore pt) (instCallE (mI, xasI)) ∧
      (v20instG P Nat).obs pt (mI, xasI) = {.diverges} ∧
      (coreInst P Nat v20).view some (ptCore pt) (instCallE (mI, xasI)) ≠
        (v20instG P Nat).obs pt (mI, xasI) := by
  have hc : Behaviour.returns [] ∈
      (coreInst P Nat v20).view some (ptCore pt) (instCallE (mI, xasI)) := by
    rw [instCallE_mI]
    exact ⟨_, core_returns P, rfl⟩
  refine ⟨pt_dom P, mI_valid, mI_some, hc, obs_pt P, fun heq => ?_⟩
  rw [heq, obs_pt P] at hc
  cases hc

/-- `pt` is not in `domInstDet g`: there the equality would hold (`obs_eq_det`). -/
theorem not_domInstDet (g : GrowKind → Nat → Nat → Nat → Bool) : ¬ domInstDet g pt :=
  fun hp => (instHost_not_eq (Profile.deterministic g)).2.2.2.2.2 (obs_eq_det g hp (mI, xasI))

/-- **`coreInstObs_sub_det` needs its closed-host behaviour**: at `Profile.deterministic g`,
`cI st` is a 2.0 instantiation run of `mI` at the domain point `pt`, and the spec observations
of the image call are not inside its mapped behaviours. -/
theorem coreInstObs_not_sub (g : GrowKind → Nat → Nat → Nat → Bool) :
    (v20instHT (Profile.deterministic g)).dom pt ∧
      Silmaril.Wasm.V2.Execution.Instantiate (Profile.deterministic g) pt.2 pt.1 mI xasI (cI st) ∧
      ¬ coreInstObs (Profile.deterministic g) (ptCore pt) (instCall (mI, xasI)) ⊆
        Behaviour.mapSet Silmaril.Wasm.V2.Execution.Val.toCore
          (Silmaril.Wasm.V2.Execution.behavioursOf (Profile.deterministic g) pt.2 (cI st)) := by
  refine ⟨pt_dom _, inst_st _, fun hsub => ?_⟩
  obtain ⟨b, hb, hmap⟩ := hsub (core_returns _)
  rw [behaviours_st _ hb] at hmap
  cases hmap

end Silmaril.Proofs.Wasm.Models.V2CoreInstHost
