module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.SpecTec.Defs

/-!
# The step charts: conditional transitions

All three transitions map a configuration `c` to its encoding `Sim.configV hn c` and are
**conditional** on the simulation conjuncts, which are not proved.

* `SpecTec.toSpec hF hB`: with both conjuncts on `D`, equal on every sentence that respects
  `CfgRel hn` (cannot tell configurations apart up to `CALL_REF` annotations).
* `SpecTec.toSpecUniv hF` / `SpecTec.toSpecExist hF`: with the forward conjunct only, SpecTec
  reflects universal respecting sentences into Core, and Core witnesses are SpecTec witnesses.
* `SpecTec.sat_iff_of_sim`: the conditional theorem, stated directly.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.SpecTec

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec

variable {env : Env} {P : Profile} {H : Type} {host : HostSemantics H} {hn : H → String}
  {D : Config H → Prop}

theorem fwd_upto (hF : FwdOn env P host hn D) (c : Config H) (hc : D c) (u : Unit) :
    ∀ b ∈ coreObs P host hn c u, ∃ b' ∈ {w | Sim.SStep env (Sim.configV hn c) w}, CfgRel hn b b' := by
  rintro b ⟨c', hs, rfl⟩
  obtain ⟨d', he, hst⟩ := hF c hc c' hs
  exact ⟨_, hst, c', d', he, rfl, rfl⟩

theorem bwd_upto (hB : BwdOn env P host hn D) (c : Config H) (hc : D c) (u : Unit) :
    ∀ b' ∈ {w | Sim.SStep env (Sim.configV hn c) w}, ∃ b ∈ coreObs P host hn c u, CfgRel hn b b' := by
  intro w hw
  obtain ⟨c', d', he, rfl, hs⟩ := hB c hc w hw
  exact ⟨_, ⟨c', hs, rfl⟩, c', d', he, rfl, rfl⟩

/-- **Conditional: Core ↔ SpecTec** on `D`, equal on `CfgRel`-respecting sentences. -/
def toSpec (hF : FwdOn env P host hn D) (hB : BwdOn env P host hn D) :
    Transition (coreChart P host hn D) (specChart env) :=
  BTrans.ofUpTo (CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial) (fwd_upto hF) (bwd_upto hB)

/-- **Conditional, forward only**: SpecTec reflects universal respecting sentences. -/
def toSpecUniv (hF : FwdOn env P host hn D) : Transition (coreChart P host hn D) (specChart env) :=
  BTrans.ofUpToUniv (CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial) (fwd_upto hF)

/-- **Conditional, forward only**: Core witnesses are SpecTec witnesses. -/
def toSpecExist (hF : FwdOn env P host hn D) : Transition (coreChart P host hn D) (specChart env) :=
  BTrans.ofUpToExist (CfgRel hn) (Sim.configV hn) id (fun _ _ => trivial) (fwd_upto hF)

/-- **The conditional theorem**: if both simulation conjuncts hold on `D`, a `CfgRel`-respecting
step sentence holds of `c ∈ D` in Core iff it holds of `configV hn c` in SpecTec. -/
theorem sat_iff_of_sim (hF : FwdOn env P host hn D) (hB : BwdOn env P host hn D) {c : Config H}
    (hc : D c) {s : BSen Unit Value} (hs : s.Respects (CfgRel hn)) :
    (coreChart P host hn D).Sat c s ↔ (specChart env).Sat (Sim.configV hn c) s :=
  (BSen.sat_iff_upto (fwd_upto hF c hc) (bwd_upto hB c hc) hs)

end Silmaril.Wasm.Atlas.SpecTec
