module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Atlas.Variant.Thms
public import Silmaril.Proofs.Wasm.Wasmi.Repro
public import Silmaril.Proofs.Wasm.Wasmi.Sim
public import Silmaril.Proofs.Wasm.Wasmi.Either

/-!
# wasmi 2.0.0 disagrees with Core, and both refine the loose model

Proofs in `Silmaril.Proofs.Wasm.Wasmi.{Fuse,Repro,SimRel,LocalGet,Sim,Either}`.

**The reproducer of issue #2046** (`reproStore`, the call `f 5 1`), at **every** profile:

* `core_f`: Core 3.0 returns `7`, and does nothing else (no trap, no divergence);
* `wasmi_f`: the wasmi model (Core 3.0 on the translated store) returns `5`, and nothing else;
* `disagree`: the safety sentence `φ7` ("every observation of `f 5 1` returns `7`") holds in
  Core and fails in the wasmi model;
* `not_conformant`, `not_complete`: neither model's observations are contained in the other's.

Both are kernel evaluations of silmaril-lean's validation, allocation and native interpreter,
transported to Core 3.0 behaviours by `Silmaril.Wasm.Interp.native_adequacy` (no native evaluation).

**The loose model** (`Loose`):

* `Loose.core_le`: every Core observation is a loose observation (every point, every host);
* `Loose.wasmi_le`: every wasmi observation is a loose observation, for hosts parametric in
  function code (silmaril-lean's `HostParametric`; the reproducer's host has no functions).
  This is a lock-step simulation from the translated code into the loose model
  (`Silmaril.Proofs.Wasm.Wasmi.behaviours_subset`), covering every Core 3.0 rule (calls into
  translated bodies, host calls, exceptions, traps, tail calls, divergence);
* `Loose.transfer`: a universal (safety) sentence of the loose model holds for Core and for
  wasmi;
* `Loose.select_either`: at the pattern with two values below, the loose model reaches either
  value; `Loose.repro`: on the reproducer it returns both `7` and `5`.

**Localisation**: `obs_of_patFree`: without the pattern, the wasmi model is Core
(`fuse` is the identity).
-/

@[expose] public section

namespace Silmaril.Wasm.Wasmi

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Atlas

variable {H : Type}

/-- **Core 3.0 on the reproducer**, every profile: `f 5 1` returns `7` and nothing else. -/
theorem core_f (P : Profile) : Core.obs P reproPt reproCall = {.returns [Val.i32 7]} :=
  Silmaril.Proofs.Wasm.Wasmi.core_f P

/-- **wasmi 2.0.0 on the reproducer**, every profile: `f 5 1` returns `5` and nothing else. -/
theorem wasmi_f (P : Profile) : obs P reproPt reproCall = {.returns [Val.i32 5]} :=
  Silmaril.Proofs.Wasm.Wasmi.wasmi_f P

/-- The safety sentence "every observation of `f 5 1` returns `7`". It is integer-only, so it
has the same meaning at every profile. -/
def φ7 : BSen Core.Call (Behaviour Val) := .always reproCall (· = .returns [Val.i32 7])

theorem φ7_universal : φ7.Universal := trivial

/-- **Disagreement**: `φ7` holds in Core 3.0 and fails in the wasmi model, at every profile. -/
theorem disagree (P : Profile) : φ7.Sat (Core.obs P reproPt) ∧ ¬ φ7.Sat (obs P reproPt) := by
  refine ⟨fun b hb => ?_, fun h => ?_⟩
  · rw [core_f] at hb
    exact hb
  · have h5 := h (.returns [Val.i32 5]) (by rw [wasmi_f]; rfl)
    exact absurd h5 (by decide)

/-- **wasmi 2.0.0 is not conformant**: at every profile, some observation of the wasmi model is
not a Core observation. -/
theorem not_conformant (P : Profile) : ¬ ∀ (x : Core.Pt Empty) c, obs P x c ⊆ Core.obs P x c := by
  intro h
  have h5 := h reproPt reproCall (show Behaviour.returns [Val.i32 5] ∈ obs P reproPt reproCall by
    rw [wasmi_f]; rfl)
  rw [core_f] at h5
  exact absurd h5 (by decide)

/-- Nor does the wasmi model have every Core observation. -/
theorem not_complete (P : Profile) : ¬ ∀ (x : Core.Pt Empty) c, Core.obs P x c ⊆ obs P x c := by
  intro h
  have h7 := h reproPt reproCall (show Behaviour.returns [Val.i32 7] ∈ Core.obs P reproPt reproCall by
    rw [core_f]; rfl)
  rw [wasmi_f] at h7
  exact absurd h7 (by decide)

/-- **Localisation**: on code without the pattern, the wasmi model is Core 3.0. -/
theorem obs_of_patFree (P : Profile) {x : Core.Pt H} (h : StorePatFree x.1) (c : Core.Call) :
    obs P x c = Core.obs P x c := by
  obtain ⟨s, host⟩ := x
  simp only [obs, Silmaril.Proofs.Wasm.Wasmi.fuseStore_of_patFree h]

/-- The reproducer is in wasmi 2.0.0's feature set. -/
theorem repro_supported : StoreSupported reproStore := by
  unfold StoreSupported; decide +kernel

/-- The reproducer's host has no functions, so it is parametric in function code. -/
theorem repro_hostParametric : HostParametric reproPt.2 :=
  fun _ _ _ _ _ _ _ _ h => h.elim

namespace Loose

/-- **Core refines the loose model**: every Core observation is a loose observation. -/
theorem core_le (P : Profile) (x : Core.Pt H) (c : Core.Call) : Core.obs P x c ⊆ obs P x c :=
  Variant.loose_mono _ _ _

/-- **wasmi refines the loose model**: every wasmi observation is a loose observation, for a
host parametric in function code. -/
theorem wasmi_le (P : Profile) {x : Core.Pt H} (hh : HostParametric x.2) (c : Core.Call) :
    Wasmi.obs P x c ⊆ obs P x c :=
  Silmaril.Proofs.Wasm.Wasmi.behaviours_subset (hh.respects (fun fi => FuncRel.refl fi)) x.1 c.1 c.2

/-- **Transfer**: a universal sentence of the loose model holds for Core and for wasmi. -/
theorem transfer (P : Profile) {x : Core.Pt H} {φ : BSen Core.Call (Behaviour Val)}
    (h : φ.Sat (obs P x)) (hu : φ.Universal) (hh : HostParametric x.2) :
    φ.Sat (Core.obs P x) ∧ φ.Sat (Wasmi.obs P x) :=
  ⟨BSen.sat_of_subset_univ (core_le P x) hu h, BSen.sat_of_subset_univ (wasmi_le P hh) hu h⟩

/-- **Either operand**: at the pattern with two values below, the loose model reaches either
value (`b = true`: the first, `b = false`: the second). -/
theorem select_either (P : Profile) (host : HostSemantics H) (b : Bool) {s : Store H}
    {f : Frame} {x : LocalIdx} {v : Val} {t : Option (List ValType)}
    (hv : f.local? x = some (some v)) (v₁ v₂ : Val) :
    Relation.ReflTransGen (Step P host) ⟨s, f, vals [v₁, v₂] ++ expression (zeroTestSel x t)⟩
      ⟨s, f, vals [if b then v₁ else v₂]⟩ :=
  Silmaril.Proofs.Wasm.Wasmi.select_either b hv v₁ v₂

/-- **On the reproducer the loose model returns both `7` and `5`.** -/
theorem repro (P : Profile) :
    Behaviour.returns [Val.i32 7] ∈ obs P reproPt reproCall ∧
      Behaviour.returns [Val.i32 5] ∈ obs P reproPt reproCall := by
  constructor
  · exact core_le P reproPt reproCall (by rw [core_f]; rfl)
  · exact wasmi_le P repro_hostParametric reproCall (by rw [wasmi_f]; rfl)

end Loose

end Silmaril.Wasm.Wasmi
