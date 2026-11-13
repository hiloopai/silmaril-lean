module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.CoreStrip.Assemble

/-!
# the three leaves hold on export-free configurations, for export-blind hosts

`leavesAt_stripped`: at a configuration without exports (`Round7.Stripped c`, round 6's domain),
for an export-blind host, `EraseFwdAt`, `EraseBwdAt` and `ExactAt` all hold. There the stripped
host is the host (`stripHostAt_of_blind`), `utf8Env` and `simEnv` agree (`Runs.agree_strip`), and
every successor 's reading is the image of an export-free witness, which erasure
fixes. So the leaves are consistent with and `wholeStepValidREH_of_leaves` specialises
to it there.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round7
open Round4Int (BI)

variable {H : Type}

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host) {nd : Bool}
  {r : RelaxedChoice}
include hinj hf hh hb

/-- At an export-free configuration, a step of the round-6 reading from its image goes to the
image of an export-free witness of a Core successor; erasure fixes that image. -/
theorem bwd_stripped {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hstr : Stripped c) {w : Value}
    (hs : Round6.Int.backend.step (BI (Profile.spec nd r) hn host) (configV hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configV hn d' ∧ Step (Profile.spec nd r) host c c' ∧
      Swap.eraseV w = w := by
  have hb₆ : Round5.Target.BoundedSel c := hstr ▸ boundedSel_strip hbc
  obtain ⟨c', d', hd, rfl, hst⟩ :=
    Round6.Target.bwdR_of_open hinj hf (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) c ts _ hc hb₆ hs
  have hd' : Stripped d' := stripped_of_configEq hd (stripped_step hb hst hstr)
  refine ⟨c', d', hd, rfl, hst, ?_⟩
  rw [Swap.eraseV_configV, hd']

/-- **The three leaves at an export-free configuration**, for an export-blind host. -/
theorem leavesAt_stripped {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hstr : Stripped c) :
    EraseFwdAt hn (Profile.spec nd r) host c ∧ EraseBwdAt hn (Profile.spec nd r) host c ∧
      ExactAt hn (Profile.spec nd r) host c := by
  have hag : ∀ w, backendE.step (BI (Profile.spec nd r) hn host) (configV hn c) w ↔
      Round6.Int.backend.step (BI (Profile.spec nd r) hn host) (configV hn c) w := by
    intro w
    have h := Runs.agree_strip (hn := hn) hb (Profile.spec nd r) c w
    rw [hstr] at h
    exact h
  rw [EraseFwdAt, EraseBwdAt, stripHostAt_of_blind hb, hstr]
  refine ⟨fun w hw => ?_, fun w₀ hw₀ => ?_, fun _ w _ hw _ => ?_⟩
  · have hs := (hag w).mp hw
    obtain ⟨-, -, -, -, -, he⟩ := bwd_stripped hinj hf hh hb hc hbc hstr hs
    rw [he]
    exact hs
  · obtain ⟨-, -, -, -, -, he⟩ := bwd_stripped hinj hf hh hb hc hbc hstr hw₀
    exact ⟨w₀, (hag w₀).mpr hw₀, he⟩
  · obtain ⟨c', d', hd, hw', hst, -⟩ := bwd_stripped hinj hf hh hb hc hbc hstr ((hag w).mp hw)
    exact ⟨c', d', hd, hw', hst⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip
