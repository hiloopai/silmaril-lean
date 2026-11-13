module

public import Silmaril.Wasm.Atlas.SpecTecR7.Defs
public import Silmaril.Wasm.Atlas.SpecTecR6.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# The SpecTec step charts at the round-7 reading: transitions

Everything here is at `Profile.spec nd r`, an injective encoding `hn`, a finite `HostOk` host that
does not observe export names (`HostExportBlind`), and 's builtins
`BI := Round4Int.BI (Profile.spec nd r) hn host`. The SpecTec chart is `Step` read in
`utf8Env BI` (`Round7.backendE`), the environment with the `$utf8` erratum.

**Unconditional, on 's domain** (export-free configurations). proved that the two
environments agree there (`Round7.Determ.envAgreeNE`), so 's transitions carry over to the
round-7 reading:

* `fwdOnR_backendE_r6`, `bwdOnR_backendE_r6`: the two halves  at `backendE`;
* `toBackendEUnivR6`, `toBackendEDetR6`: the transitions, universal and (on `DomDet`) equal;
* `sat_iff_backendE_det_r6`: on a valid, `BoundedSel`, deterministic configuration a
  `CfgRel`-respecting step sentence holds in Core iff it holds of the image under `Step` in
  `utf8Env BI`;
* `readChart_sat_backendE_iff`: on 's domain the two readings satisfy the same sentences.

**Conditional, on the restated round-7 domain `DomE`** (module instances may export names). The
host is also asked to be export-parametric (`HostExportParam`). Every transition takes
`hS : Round7.Task.swapEquiv`. This premise is proved by
`Round7.EraseDer.swapEquiv_holds`; `Atlas.SpecTecR7U` applies that proof to the wrappers below.
The alternative adapter from `Round7.Swap.Task.stepErase` uses
`Round7.Swap.swapEquiv_of_stepErase`; that premise is also proved by
`Round7.EraseDer.stepErase_holds`:

* `fwdOnR_backendE`, `bwdOnR_backendE`: the two halves of `Round7.Task.wholeStepValidREI` at the
  concrete builtins (`Round7.fwdREI_of_leaves`, `bwdREI_of_leaves` with `envAgreeNE`);
* `toBackendEUniv`, `toBackendEExist`, `toBackendEDet`: the transitions, as in `Atlas.SpecTecR6`;
* `sat_iff_backendE_det`, `sat_backendE_of_univ`: the step theorem stated directly, and
  `sat_iff_backendE_det_of_stepErase` from the leaf.

Run transitions are in `Atlas.SpecTecR7Runs`: `RunDomE` requires validity plus `BoundedSelE`
and `StripInj` at every reachable configuration; equality adds determinism throughout that set.
`Atlas.SpecTecR7RunsM` replaces export-parametricity with `HostModsSub`. Its source-only
wrappers require `StripInj` and `NamesBnd` only at the source, while retaining selection bounds
throughout reachability and, for equality, determinism there.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.SpecTec.Sim.Round6 (Target.Reading)
open Silmaril.Wasm.Atlas.SpecTecR6 (readChart FwdOnR BwdOnR Dom DomDet StepDet bwd_upto fwd_upto_det)

variable {H : Type} {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

/-- Two readings with the same successors at `v` satisfy the same sentences at `v`. -/
theorem readChart_sat_congr {Rd Rd' : Target.Reading} {B : Builtins} {v : Value}
    (h : ∀ w, Rd.step B v w ↔ Rd'.step B v w) (s : BSen Unit Value) :
    (readChart Rd B).Sat v s ↔ (readChart Rd' B).Sat v s := by
  have e : (fun _ : Unit => {w | Rd.step B v w}) = fun _ => {w | Rd'.step B v w} :=
    funext fun _ => Set.ext h
  show s.Sat (fun _ => {w | Rd.step B v w}) ↔ s.Sat (fun _ => {w | Rd'.step B v w})
  rw [e]

/-! ## On 's domain (unconditional) -/

section R6

/-- On 's domain, `Step` reads alike in `utf8Env BI` and `simEnv BI`. -/
theorem backendE_iff_backend (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) (w : Value) :
    Sim.Round7.backendE.step (Sim.Round4Int.BI (Profile.spec nd r) hn host) (Sim.configV hn c) w ↔
      Sim.Round6.Int.backend.step (Sim.Round4Int.BI (Profile.spec nd r) hn host)
        (Sim.configV hn c) w := by
  obtain ⟨⟨ts, hok⟩, hsel, -⟩ := hc
  exact Sim.Round7.Determ.envAgreeNE _ hn hinj host hf hh hb nd r c ts hok hsel w

/-- **'s forward half at the round-7 reading.** -/
theorem fwdOnR_backendE_r6 (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) :
    FwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host) := by
  intro c hc c' hs
  obtain ⟨c'', hs', hu, d', he, hst⟩ := SpecTecR6.fwdOnR_backend hinj hf hh c hc c' hs
  exact ⟨c'', hs', hu, d', he, (backendE_iff_backend hinj hf hh hb hc _).2 hst⟩

/-- **'s backward half at the round-7 reading.** -/
theorem bwdOnR_backendE_r6 (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) :
    BwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host) :=
  fun c hc w hs => SpecTecR6.bwdOnR_backend hinj hf hh c hc w
    ((backendE_iff_backend hinj hf hh hb hc w).1 hs)

/-- **Core → SpecTec (round-7 reading), universal**, on 's domain. -/
noncomputable def toBackendEUnivR6 (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (bwd_upto (bwdOnR_backendE_r6 hinj hf hh hb))

/-- **Core ↔ SpecTec (round-7 reading) on 's deterministic domain**: equal on every
`CfgRel`-respecting step sentence. Unconditional. -/
noncomputable def toBackendEDetR6 (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (fwd_upto_det (fun c hc => fwdOnR_backendE_r6 hinj hf hh hb c hc.1) (fun _ hc => hc.2))
    (bwd_upto (fun c hc => bwdOnR_backendE_r6 hinj hf hh hb c hc.1))

theorem toBackendEDetR6_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) :
    (toBackendEDetR6 (nd := nd) (r := r) hinj hf hh hb).dir = .equal := rfl

/-- **The round-6 step theorem at the round-7 reading**: on a valid, `BoundedSel`, deterministic
configuration a `CfgRel`-respecting step sentence holds in Core iff it holds of the image under
`Step` in `utf8Env BI`. -/
theorem sat_iff_backendE_det_r6 (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) {c : Config H}
    (hc : DomDet (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart (Profile.spec nd r) host hn (DomDet (Profile.spec nd r) host)).Sat c s ↔
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendEDetR6, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendEDetR6 hinj hf hh hb).sat_iff rfl hc hs

/-- **The two readings agree on 's domain**, on every sentence. -/
theorem readChart_sat_backendE_iff (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host) {c : Config H}
    (hc : Dom (Profile.spec nd r) host c) (s : BSen Unit Value) :
    (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s ↔
      (readChart Sim.Round6.Int.backend (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  readChart_sat_congr (backendE_iff_backend hinj hf hh hb hc) s

end R6

/-! ## On the restated round-7 domain (conditional on `Round7.Task.swapEquiv`) -/

section R7

variable (hS : Sim.Round7.Task.swapEquiv)
include hS

/-- **The forward half of `Round7.Task.wholeStepValidREI`** on `DomE`, at the concrete builtins. -/
theorem fwdOnR_backendE (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    FwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host) :=
  fun c ⟨⟨ts, hc⟩, hbc, hic, hsucc⟩ c' hs =>
    Sim.Round7.fwdREI_of_leaves hS Sim.Round7.Determ.envAgreeNE hinj hf hh hb hp c c' ts hc hbc
      hic hsucc hs

/-- **The backward half of `Round7.Task.wholeStepValidREI`** on `DomE`, at the concrete
builtins. -/
theorem bwdOnR_backendE (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    BwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host) :=
  fun c ⟨⟨ts, hc⟩, hbc, hic, _⟩ w hs =>
    Sim.Round7.bwdREI_of_leaves hS Sim.Round7.Determ.envAgreeNE hinj hf hh hb hp c ts w hc hbc
      hic hs

/-- **Core → SpecTec (round-7 reading), universal**, on `DomE`. -/
noncomputable def toBackendEUniv (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToUniv (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (bwd_upto (bwdOnR_backendE hS hinj hf hh hb hp))

/-- **Core → SpecTec (round-7 reading), existential**, on `DomE`. -/
noncomputable def toBackendEExist (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofSupUpToExist (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (bwd_upto (bwdOnR_backendE hS hinj hf hh hb hp))

/-- **Core ↔ SpecTec (round-7 reading) on `DomDetE`**: equal on every `CfgRel`-respecting step
sentence. -/
noncomputable def toBackendEDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomDetE (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  BTrans.ofUpTo (SpecTec.CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial)
    (fwd_upto_det (fun c hc => fwdOnR_backendE hS hinj hf hh hb hp c hc.1) (fun _ hc => hc.2))
    (bwd_upto (fun c hc => bwdOnR_backendE hS hinj hf hh hb hp c hc.1))

theorem toBackendEDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    (toBackendEDet (nd := nd) (r := r) hS hinj hf hh hb hp).dir = .equal := rfl

/-- **The restated round-7 step theorem, stated directly** (conditional on `Task.swapEquiv`): on a
valid, `BoundedSelE`, `StripInj`, deterministic configuration with `BoundedSelE` successors, a
`CfgRel`-respecting step sentence holds in Core iff it holds of the image under `Step` in
`utf8Env BI`. -/
theorem sat_iff_backendE_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : DomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart (Profile.spec nd r) host hn (DomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  by simpa only [toBackendEDet, BTrans.ofUpTo, BSen.rename_id] using
    (toBackendEDet hS hinj hf hh hb hp).sat_iff rfl hc hs

/-- **Core safety transfers to the round-7 reading** on `DomE` (no determinism needed). -/
theorem sat_backendE_of_univ (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : DomE (Profile.spec nd r) host c) {s : BSen Unit Value} (hu : s.Universal)
    (hs : s.Respects (SpecTec.CfgRel hn))
    (h : (SpecTec.coreChart (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host)).Sat c s) :
    (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
      (Sim.configV hn c) s :=
  by simpa only [toBackendEUniv, BTrans.ofSupUpToUniv, BSen.rename_id] using
    (toBackendEUniv hS hinj hf hh hb hp).transfer rfl hc ⟨hu, hs⟩ h

end R7

/-- **The restated round-7 step theorem from an explicit evaluator premise**
`Round7.Swap.Task.stepErase`, proved by `Round7.EraseDer.stepErase_holds`. The wrapper
`Atlas.SpecTecR7U.sat_iff_backendE_det` instead supplies `swapEquiv_holds` directly. -/
theorem sat_iff_backendE_det_of_stepErase (hE : Sim.Round7.Swap.Task.stepErase)
    (hinj : Function.Injective hn) (hf : Sim.HostFinite host) (hh : HostOk host)
    (hb : Sim.Round7.HostExportBlind host) (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : DomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart (Profile.spec nd r) host hn (DomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  sat_iff_backendE_det (Sim.Round7.Swap.swapEquiv_of_stepErase hE) hinj hf hh hb hp hc hs

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7.sat_iff_backendE_det_r6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_det_r6

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7.readChart_sat_backendE_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readChart_sat_backendE_iff

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7.sat_iff_backendE_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_det

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7.sat_iff_backendE_det_of_stepErase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_det_of_stepErase

end Silmaril.Wasm.Atlas.SpecTecR7
