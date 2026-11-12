module

public import Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostStrict.Basic
public import Silmaril.Wasm.Atlas.SpecTecR7RunsM.Thms

/-!
# `HostModsSub` is strictly weaker than `HostExportParam` (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict`; see `docs/projects/spectec/README.md`, "re
". The host `cloneHost` is in `Round7/HostStrict/Defs.lean`.

* `cloneHost_finite`, `cloneHost_ok`, `cloneHost_blind`, `cloneHost_modsSub`: it is finite,
  `HostOk`, export-blind and invents no module.
* `cloneHost_not_param`: it is not export-parametric, at every `H` with a function instance and
  a host function.
* `hostModsSub_strict`: a host on `Unit` with the first four properties and not the fifth.
  `not_param_of_modsSub` is the same fact as a refuted implication.
* `sat_iff_cloneHost`: the run theorem with `HostModsSub`
  (`Atlas.SpecTecR7RunsM.sat_iff_backendE_runs_src`) applies to `cloneHost`. The old one
  (`Atlas.SpecTecR7Runs.sat_iff_backendE_runs_det`) does not, since its hypothesis
  `HostExportParam` fails.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.SpecTec.Sim.Round7.HostMods (HostModsSub)
open Silmaril.Wasm.Atlas (BSen)
open Silmaril.Wasm.Atlas.SpecTecR6 (runChart readRunChart)

/-- A host function instance on `Unit`. -/
def unitFI : FuncInst Unit := { type := .defn (.group .nil) 0, module := {}, code := .host () }

/-- **`HostModsSub` is strictly weaker than `HostExportParam`**, among finite, `HostOk`,
export-blind hosts. -/
theorem hostModsSub_strict :
    ∃ host : HostSemantics Unit, HostFinite host ∧ HostOk host ∧ HostExportBlind host ∧
      HostModsSub host ∧ ¬ HostExportParam host :=
  ⟨cloneHost, cloneHost_finite, cloneHost_ok, cloneHost_blind, cloneHost_modsSub,
    cloneHost_not_param unitFI ()⟩

/-- **Refuted**: a finite, `HostOk`, export-blind host that invents no module need not be
export-parametric. -/
theorem not_param_of_modsSub :
    ¬ ∀ (H : Type) (host : HostSemantics H), HostFinite host → HostOk host →
      HostExportBlind host → HostModsSub host → HostExportParam host := fun h =>
  cloneHost_not_param unitFI () (h Unit cloneHost cloneHost_finite cloneHost_ok cloneHost_blind
    cloneHost_modsSub)

/-- **The run theorem with `HostModsSub` applies to `cloneHost`**: on `RunSrcDetE`, a
`CfgRel`-respecting reachability sentence holds in Core iff it holds of the image under the runs
of `Step` in `utf8Env BI`. -/
theorem sat_iff_cloneHost {H : Type} {hn : H → String} (hinj : Function.Injective hn)
    {nd : Bool} {r : RelaxedChoice} {c : Config H}
    (hc : Atlas.SpecTecR7RunsM.RunSrcDetE (Profile.spec nd r) cloneHost c) {s : BSen Unit Value}
    (hs : s.Respects (Silmaril.Wasm.Atlas.SpecTec.CfgRel hn)) :
    (runChart (Profile.spec nd r) cloneHost hn
        (Atlas.SpecTecR7RunsM.RunSrcDetE (Profile.spec nd r) cloneHost)).Sat c s ↔
      (readRunChart backendE (Round4Int.BI (Profile.spec nd r) hn cloneHost)).Sat
        (configV hn c) s :=
  Atlas.SpecTecR7RunsM.sat_iff_backendE_runs_src hinj cloneHost_finite cloneHost_ok
    cloneHost_blind cloneHost_modsSub hc hs

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.hostModsSub_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hostModsSub_strict

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.not_param_of_modsSub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_param_of_modsSub

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict.sat_iff_cloneHost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sat_iff_cloneHost

end Silmaril.Wasm.SpecTec.Sim.Round7.HostStrict
