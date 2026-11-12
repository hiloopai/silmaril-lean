module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Runs.Step

/-!
# Round 7, runs: the multi-step corollary at the round-7 reading

`runsRE`: from a valid source every configuration Core reaches from which is `BoundedSelE` and
`StripInj` (`ReachE`), for an injective `hn` and a finite, `HostOk`, export-blind and
export-parametric host, at `B := BI (Profile.spec nd r) hn host`:

* every deterministic Core run (`Round6.Target.DetSteps`) is a run of `Round7.backendE` up to
  `Bwd.ConfigEq`;
* every run of `Round7.backendE` is the image of a Core run up to `Bwd.ConfigEq`.

It is round 6's `runsR_backend` with module instances that export names. The induction threads
`RelE` (`fwdRelE`, `bwdRelE`); it starts at `RelE c₀ c₀` (`relE_refl`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.Target (DetSteps RSteps)
open Round4Int (BI)

variable {H : Type}

/-- **A valid, `BoundedSelE` configuration is its own `RelE` witness.** -/
theorem relE_refl {P : Profile} {hn : H → String} {host : HostSemantics H} {c : Config H}
    {ts : List CValType} (hc : ConfigOk c ts) (hb : BoundedSelE c) :
    RelE (BI P hn host) hn c c :=
  ⟨Bwd.ConfigEq.refl c, Round5.Target.typed_of_configOk_sel _ hn (configOk_strip hc)
    (boundedSel_strip hb)⟩

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hp : HostExportParam host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hp

/-- **Deterministic Core runs are runs of the round-7 reading, along `RelE`.** -/
theorem stepsRE_sim {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hR : ReachE (Profile.spec nd r) host c₀)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c₀ d₀) {c : Config H}
    (hs : DetSteps (Profile.spec nd r) host c₀ c) :
    ∃ d, RelE (BI (Profile.spec nd r) hn host) hn c d ∧
      RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn d₀) (configV hn d) := by
  induction hs with
  | refl => exact ⟨d₀, hd, .refl⟩
  | @tail c₁ c₂ h₁ h₂ ih =>
    obtain ⟨d₁, hr₁, hr⟩ := ih
    have hrun : Steps (Profile.spec nd r) host c₀ c₁ := Round6.Target.steps_of_detSteps h₁
    obtain ⟨hb₁, hi₁⟩ := hR c₁ hrun
    obtain ⟨d₂, hr₂, hst⟩ := fwdRelE hinj hf hh hb hp c₁ d₁ c₂ ts (Steps.safe hh hc hrun).1 hb₁
      hi₁ (fun c' h' => (hR c' (hrun.tail h')).1) hr₁ h₂.1 h₂.2
    exact ⟨d₂, hr₂, hr.tail hst⟩

/-- **Runs of the round-7 reading are Core runs, along `RelE`.** -/
theorem sstepsRE_sim {c₀ d₀ : Config H} {ts : List CValType} (hc : ConfigOk c₀ ts)
    (hR : ReachE (Profile.spec nd r) host c₀)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c₀ d₀) {w : Value}
    (hs : RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn d₀) w) :
    ∃ c d, RelE (BI (Profile.spec nd r) hn host) hn c d ∧ w = configV hn d ∧
      Steps (Profile.spec nd r) host c₀ c := by
  induction hs with
  | refl => exact ⟨c₀, d₀, hd, rfl, .refl⟩
  | @tail w₁ w₂ _ h₂ ih =>
    obtain ⟨c₁, d₁, hr₁, rfl, hs₁⟩ := ih
    obtain ⟨hb₁, hi₁⟩ := hR c₁ hs₁
    obtain ⟨c₂, d₂, hr₂, hw, hst⟩ := bwdRelE hinj hf hh hb hp c₁ d₁ ts w₂
      (Steps.safe hh hc hs₁).1 hb₁ hi₁ (fun c' h' => (hR c' (hs₁.tail h')).1) hr₁ h₂
    exact ⟨c₂, d₂, hr₂, hw, hs₁.tail hst⟩

/-- **The multi-step corollary at the round-7 reading.** From a valid source whose reachable
configurations are all `BoundedSelE` and `StripInj`: deterministic Core runs are runs of
`Round7.backendE` up to `Bwd.ConfigEq`, and runs of `Round7.backendE` are Core runs up to
`Bwd.ConfigEq`. -/
theorem runsRE :
    (∀ (c₀ c : Config H) (ts : List CValType), ConfigOk c₀ ts →
      ReachE (Profile.spec nd r) host c₀ → DetSteps (Profile.spec nd r) host c₀ c →
      ∃ d, Bwd.ConfigEq c d ∧
        RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn c₀) (configV hn d)) ∧
    (∀ (c₀ : Config H) (ts : List CValType) (w : Value), ConfigOk c₀ ts →
      ReachE (Profile.spec nd r) host c₀ →
      RSteps backendE (BI (Profile.spec nd r) hn host) (configV hn c₀) w →
      ∃ c d, Bwd.ConfigEq c d ∧ w = configV hn d ∧ Steps (Profile.spec nd r) host c₀ c) := by
  refine ⟨fun c₀ c ts hc hR hs => ?_, fun c₀ ts w hc hR hs => ?_⟩
  · obtain ⟨d, hr, hss⟩ := stepsRE_sim hinj hf hh hb hp hc hR
      (relE_refl hc (hR c₀ .refl).1) hs
    exact ⟨d, hr.1, hss⟩
  · obtain ⟨c, d, hr, hw, hss⟩ := sstepsRE_sim hinj hf hh hb hp hc hR
      (relE_refl hc (hR c₀ .refl).1) hs
    exact ⟨c, d, hr.1, hw, hss⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
