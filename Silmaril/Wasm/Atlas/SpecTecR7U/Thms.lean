module

public import Silmaril.Wasm.Atlas.SpecTecR7.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Thms

/-!
# The SpecTec step charts at the round-7 reading, unconditionally

`Atlas.SpecTecR7` wires the round-7 reading of SpecTec's `Step` (`Round7.backendE`, `utf8Env BI`)
on the restated domain `DomE` (module instances may export names) conditionally on
`Round7.Task.swapEquiv`. That leaf is now proved (`Round7.EraseDer.swapEquiv_holds`, from
`Round7.EraseDer.stepHost_holds`), so the transitions hold outright, for an injective `hn` and a
finite, `HostOk`, export-blind (`HostExportBlind`) and export-parametric (`HostExportParam`) host:

* `fwdOnR_backendE`, `bwdOnR_backendE`: the two halves of `Round7.Task.wholeStepValidREI` on
  `DomE`, at the concrete builtins;
* `toBackendEDet`: Core and the round-7 reading agree on `DomDetE` (direction `equal`);
* `sat_iff_backendE_det`: on a valid, `BoundedSelE`, `StripInj`, deterministic configuration with
  `BoundedSelE` successors, a `CfgRel`-respecting step sentence holds in Core iff it holds of the
  image under `Step` in `utf8Env BI`;
* `sat_backendE_of_univ`: universal sentences transfer from Core on `DomE`.

These step wrappers retain `StripInj` in the domain and `HostExportParam` as a host premise.
Run adapters are provided separately by `Atlas.SpecTecR7Runs`: validity, `BoundedSelE` and
`StripInj` throughout reachability give universal transfer on `CfgRel`-respecting sentences;
determinism throughout that set gives equality on respecting sentences. `Atlas.SpecTecR7RunsM` uses `HostModsSub`
instead of `HostExportParam`; its source-only wrappers require `StripInj`/`NamesBnd` at the
source, selection bounds throughout reachability, and determinism there for equality. Both
run families retain the injective encoding, finite `HostOk`, export-blind host and
`Profile.spec nd r` premises.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTecR7U

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec
open Silmaril.Wasm.Atlas.SpecTecR6 (readChart FwdOnR BwdOnR)
open Silmaril.Wasm.Atlas.SpecTecR7 (DomE DomDetE)

variable {H : Type} {hn : H → String} {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}

/-- **The forward half of `Round7.Task.wholeStepValidREI`** on `DomE`, unconditionally. -/
theorem fwdOnR_backendE (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    FwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host) :=
  SpecTecR7.fwdOnR_backendE Sim.Round7.EraseDer.swapEquiv_holds hinj hf hh hb hp

/-- **The backward half of `Round7.Task.wholeStepValidREI`** on `DomE`, unconditionally. -/
theorem bwdOnR_backendE (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    BwdOnR Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)
      (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host) :=
  SpecTecR7.bwdOnR_backendE Sim.Round7.EraseDer.swapEquiv_holds hinj hf hh hb hp

/-- **Core ↔ SpecTec (round-7 reading) on `DomDetE`**, unconditionally. -/
noncomputable def toBackendEDet (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    Transition (SpecTec.coreChart (Profile.spec nd r) host hn (DomDetE (Profile.spec nd r) host))
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)) :=
  SpecTecR7.toBackendEDet Sim.Round7.EraseDer.swapEquiv_holds hinj hf hh hb hp

theorem toBackendEDet_dir (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) :
    (toBackendEDet (nd := nd) (r := r) hinj hf hh hb hp).dir = .equal := rfl

/-- **The restated round-7 step theorem**, unconditionally: on a valid, `BoundedSelE`, `StripInj`,
deterministic configuration with `BoundedSelE` successors, a `CfgRel`-respecting step sentence
holds in Core iff it holds of the image under `Step` in `utf8Env BI`. -/
theorem sat_iff_backendE_det (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : DomDetE (Profile.spec nd r) host c) {s : BSen Unit Value}
    (hs : s.Respects (SpecTec.CfgRel hn)) :
    (SpecTec.coreChart (Profile.spec nd r) host hn (DomDetE (Profile.spec nd r) host)).Sat c s ↔
      (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
        (Sim.configV hn c) s :=
  SpecTecR7.sat_iff_backendE_det Sim.Round7.EraseDer.swapEquiv_holds hinj hf hh hb hp hc hs

/-- **Core safety transfers to the round-7 reading** on `DomE`, unconditionally. -/
theorem sat_backendE_of_univ (hinj : Function.Injective hn) (hf : Sim.HostFinite host)
    (hh : HostOk host) (hb : Sim.Round7.HostExportBlind host)
    (hp : Sim.Round7.HostExportParam host) {c : Config H}
    (hc : DomE (Profile.spec nd r) host c) {s : BSen Unit Value} (hu : s.Universal)
    (hs : s.Respects (SpecTec.CfgRel hn))
    (h : (SpecTec.coreChart (Profile.spec nd r) host hn (DomE (Profile.spec nd r) host)).Sat c s) :
    (readChart Sim.Round7.backendE (Sim.Round4Int.BI (Profile.spec nd r) hn host)).Sat
      (Sim.configV hn c) s :=
  SpecTecR7.sat_backendE_of_univ Sim.Round7.EraseDer.swapEquiv_holds hinj hf hh hb hp hc hu hs h

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7U.sat_iff_backendE_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_backendE_det

/-- info: 'Silmaril.Wasm.Atlas.SpecTecR7U.sat_backendE_of_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_backendE_of_univ

end Silmaril.Wasm.Atlas.SpecTecR7U
