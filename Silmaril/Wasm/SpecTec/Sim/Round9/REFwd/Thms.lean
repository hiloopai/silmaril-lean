module

public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round9.BadN.Thms

/-!
# RE: the forward leaf at export-blind hosts from `BadFwdN`

Integration , an earlier step (`w9-p2-re` with `w9-p2-re-core`); see `docs/projects/spectec/README.md`,
"Round 9 status".

* **`eraseFwdAt_of_blindN`**: at an export-blind host, `CoreStrip.EraseFwdAt` follows from
  `BadN.BadFwdN` (7 rules) alone. This is `CoreStrip.eraseFwdAt_of_blind` with `BadFwdE` and
  `ElseBwdBLeft''` discharged by `w9-p2-re` (`BadN.sStepB_fwd_BI_N`, which uses
  `ElseRef.elseBwdB_holds` and `BadN.badFwdE_of_N`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.REFwd

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7
open Round9.CoreStrip

variable {H : Type}

/-- **The forward SpecTec leaf of RE at an export-blind host, from the 7 rules of `BadFwdN`.** -/
theorem eraseFwdAt_of_blindN {hn : H → String} {host : HostSemantics H}
    (hb : HostExportBlind host) (P : Profile)
    (hN : BadN.BadFwdN (NxPrims.envBI P hn host)) (c : Config H) :
    EraseFwdAt hn P host c := by
  intro w hw
  have h₁ := BadN.sStepB_fwd_BI_N P hn host hN hw
  rw [Swap.eraseV_configV] at h₁
  rw [stripHostAt_of_blind hb]
  exact (Runs.agree_strip hb P c _).mp h₁

end Silmaril.Wasm.SpecTec.Sim.Round9.REFwd

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.REFwd.eraseFwdAt_of_blindN' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Silmaril.Wasm.SpecTec.Sim.Round9.REFwd.eraseFwdAt_of_blindN
