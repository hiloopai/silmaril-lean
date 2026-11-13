module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.SpecTecR6.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms

/-!
# The SpecTec step charts at the backend reading: unconditional transitions

`Round6.Int.wholeStepValidR_backend` and `Round6.Int.runsR_backend` (proved ) wired
into the atlas. Everything here is at `Profile.spec nd r`, an injective encoding `hn`, a finite
`HostOk` host and the concrete builtins `BI := Round4Int.BI (Profile.spec nd r) hn host`. No
hypothesis is left open: these replace the conditional `SpecTec.toSpec` on the valid fragment.

One step (`coreChart … (Dom …)` → `readChart backend BI`):

* `fwdOnR_backend`, `bwdOnR_backend`: the two halves of the round-6 theorem as `FwdOnR`/`BwdOnR`.
* `toBackendUniv`: every SpecTec successor is related by `CfgRel` to a Core successor, so Core's
  universal, `CfgRel`-respecting sentences hold in SpecTec (direction `preserves`).
* `toBackendExist`: dually, SpecTec's existential respecting witnesses are Core witnesses
  (direction `reflects`).
* `toBackendDet`: on `DomDet` (Core has at most one successor) the forward half is exact, and the
  transition is **equal** on every `CfgRel`-respecting sentence (`sat_iff_backend_det`).

Runs (`runChart … RunDom` → `readRunChart backend BI`):

* `toBackendRunsUniv`: from `runsR_backend`'s backward half, Core's universal respecting
  reachability sentences hold of SpecTec's runs.
* `toBackendRunsDet`: on `RunDomDet` every Core run is deterministic (`detSteps_of_steps`), so
  `runsR_backend`'s forward half applies and the run transition is **equal** on `CfgRel`-respecting
  sentences (`sat_iff_backend_runs_det`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR6

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.SpecTec.Sim.Round6 (Target.Reading Target.DetSteps Target.RSteps)

variable {H : Type} {P : Profile} {host : HostSemantics H} {hn : H → String}
  {Rd : Target.Reading} {B : Builtins} {D : Config H → Prop}

/-! ## Generic: from the conjuncts to observation inclusions -/

theorem bwd_upto (hB : BwdOnR Rd B P host hn D) (c : Config H) (hc : D c) (u : Unit) :
    ∀ b' ∈ {w | Rd.step B (Sim.configV hn c) w},
      ∃ b ∈ SpecTec.coreObs P host hn c u, SpecTec.CfgRel hn b b' := by
  intro w hw
  obtain ⟨c', d', he, rfl, hs⟩ := hB c hc w hw
  exact ⟨_, ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

/-- On configurations with at most one Core successor, the forward conjunct is exact. -/
theorem fwd_upto_det (hF : FwdOnR Rd B P host hn D) (hD : ∀ c, D c → StepDet P host c)
    (c : Config H) (hc : D c) (u : Unit) :
    ∀ b ∈ SpecTec.coreObs P host hn c u,
      ∃ b' ∈ {w | Rd.step B (Sim.configV hn c) w}, SpecTec.CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨c'', -, hu, d', he, hst⟩ := hF c hc c' hs
  have e : c'' = c' := hu fun c₃ h₃ => hD c hc c₃ c' h₃ hs
  subst e
  exact ⟨_, hst, c'', d', he, rfl, rfl⟩

/-- A Core run through configurations that each have at most one successor is a deterministic
run. -/
theorem detSteps_of_steps {c c' : Config H} (h : Steps P host c c')
    (hd : ∀ c'', Steps P host c c'' → StepDet P host c'') :
    Sim.Round6.Target.DetSteps P host c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hs _ ih =>
    exact .head ⟨hs, fun c₃ h₃ => hd _ .refl _ _ h₃ hs⟩
      (ih fun c'' h'' => hd c'' (.head hs h''))

/-! ## The round-6 conjuncts at the backend reading -/

section Backend

variable {nd : Bool} {r : RelaxedChoice}

/-- **The forward half of `wholeStepValidR_backend`** on `Dom`, at the concrete builtins. -/
theorem fwdOnR_backend (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    FwdOnR Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host) :=
  fun c ⟨⟨ts, hc⟩, hb, hsucc⟩ c' hs =>
    Sim.Round6.Target.fwdR_of_open hinj hf hh (Sim.Round6.Int.openR_backend hinj hf hh)
      c c' ts hc hb hsucc hs

/-- **The backward half of `wholeStepValidR_backend`** on `Dom`, at the concrete builtins. -/
theorem bwdOnR_backend (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    BwdOnR Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host) :=
  fun c ⟨⟨ts, hc⟩, hb, _⟩ w hs =>
    Sim.Round6.Target.bwdR_of_open hinj hf (Sim.Round5.BwdStep.growMaySucceed_spec nd r)
      (Sim.Round4.growMayFail_spec nd r) (Sim.Round6.Int.openR_backend hinj hf hh) c ts w hc hb hs

/-! ## One-step transitions -/

/-- **Core → SpecTec (backend), universal**: Core's universal `CfgRel`-respecting step sentences
hold of the SpecTec image, on the whole round-6 domain. -/
noncomputable def toBackendUniv (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (bwd_upto (bwdOnR_backend hinj hf hh))

/-- **Core → SpecTec (backend), existential**: SpecTec's existential respecting witnesses are
Core witnesses. -/
noncomputable def toBackendExist (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToExist (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (bwd_upto (bwdOnR_backend hinj hf hh))

/-- **Core ↔ SpecTec (backend) on deterministic configurations**: equal on every
`CfgRel`-respecting step sentence. Unconditional. -/
noncomputable def toBackendDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host))
      (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (fwd_upto_det (fun c hc => fwdOnR_backend hinj hf hh c hc.1) (fun _ hc => hc.2))
    (bwd_upto (fun c hc => bwdOnR_backend hinj hf hh c hc.1))

theorem toBackendDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) : (toBackendDet (nd := nd) (r := r) hinj hf hh).dir = .equal := rfl

/-- **The step theorem, stated directly**: on a valid, `BoundedSel` configuration with
`BoundedSel` successors and at most one Core successor, a `CfgRel`-respecting step sentence holds
in Core iff it holds of the image under the backend reading of SpecTec. -/
theorem sat_iff_backend_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host)).Sat c s ↔
      (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendDet, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendDet hinj hf hh).sat_iff rfl hc hs

/-- **Core safety transfers to SpecTec** on the whole round-6 domain (no determinism needed). -/
theorem sat_backend_of_univ (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) {c : Config H} (hc : Dom (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hu : s.Universal) (hs : s.Respects (SpecTec.CfgRel hn))
    (h : (SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host)).Sat c s) :
    (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
      (Sim.configV hn c) s :=
  by simpa only [toBackendUniv, BTrans.ofSupUpToUniv, BSen.rename_id] using
    (toBackendUniv hinj hf hh).transfer rfl hc ⟨hu, hs⟩ h

/-! ## Run transitions -/

theorem runs_bwd_upto (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (c : Config H) (hc : RunDom (Profile.spec nd r) host c) (u : Unit) :
    ∀ b' ∈ readRunObs Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u,
      ∃ b ∈ runObs (Profile.spec nd r) host hn c u, SpecTec.CfgRel hn b b' := by
  intro w hw
  obtain ⟨ts, hok⟩ := hc.1
  obtain ⟨c', d', he, rfl, hs⟩ := (Sim.Round6.Int.runsR_backend hinj hf hh).2 c ts w hok hc.2 hw
  exact ⟨_, ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

theorem runs_fwd_upto_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (c : Config H) (hc : RunDomDet (Profile.spec nd r) host c) (u : Unit) :
    ∀ b ∈ runObs (Profile.spec nd r) host hn c u,
      ∃ b' ∈ readRunObs Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) u, SpecTec.CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨ts, hok⟩ := hc.1.1
  obtain ⟨d, he, hrun⟩ := (Sim.Round6.Int.runsR_backend hinj hf hh).1 c c' ts hok hc.1.2
    (detSteps_of_steps hs hc.2)
  exact ⟨_, hrun, c', d, he, rfl, rfl⟩

/-- **Core runs → SpecTec (backend) runs, universal**: Core's universal respecting reachability
sentences hold of SpecTec's runs, from every valid source whose reachable set is `BoundedSel`. -/
noncomputable def toBackendRunsUniv (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDom (Profile.spec nd r) host))
      (readRunChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runs_bwd_upto hinj hf hh)

/-- **Core runs ↔ SpecTec (backend) runs on deterministic sources**: equal on every
`CfgRel`-respecting reachability sentence. -/
noncomputable def toBackendRunsDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) :
    Transition (runChart (Profile.spec nd r) host hn (RunDomDet (Profile.spec nd r) host))
      (readRunChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (runs_fwd_upto_det hinj hf hh) (fun c hc => runs_bwd_upto hinj hf hh c hc.1)

theorem toBackendRunsDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) : (toBackendRunsDet (nd := nd) (r := r) hinj hf hh).dir = .equal := rfl

/-- **The run theorem, stated directly**: from a valid source whose reachable configurations are
all `BoundedSel` and have at most one Core successor, a `CfgRel`-respecting reachability sentence
holds in Core iff it holds of the image under the backend reading's runs. -/
theorem sat_iff_backend_runs_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) {c : Config H} (hc : RunDomDet (Profile.spec nd r) host c)
    {s : BSen Unit Value} (hs : s.Respects (SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) host hn (RunDomDet (Profile.spec nd r) host)).Sat c s ↔
      (readRunChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendRunsDet, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendRunsDet hinj hf hh).sat_iff rfl hc hs

end Backend

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR6.sat_iff_backend_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backend_det

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR6.sat_backend_of_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_backend_of_univ

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR6.sat_iff_backend_runs_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backend_runs_det

end Silmaril.Wasm.Atlas.SpecTecR6
