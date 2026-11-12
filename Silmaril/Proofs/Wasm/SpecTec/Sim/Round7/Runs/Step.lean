module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Runs.Swap
public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Int.Final.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 7, runs: one step along `RelE`

The one-step halves of `Round7.Task.wholeStepValidREI`, from every `RelE` witness `d` of a valid
configuration `c` rather than from `c` itself. The route is that of
`Round7.fwdREI_of_leaves`/`bwdREI_of_leaves`, with round 6's relational steps
(`Round6.Target.fwdRelR_of_open`, `bwdRelR_of_open`) in place of its steps at `c`:

1. `stripConfig d` is a `Round4.SimRel` witness of `stripConfig c` (`simRel_strip`);
2. round 6 steps from it in `simEnv BI`;
3. `utf8Env BI` and `simEnv BI` agree there, since it is export-free (`agree_strip`);
4. the export swap at `d` (`swapAt_fwd`, `swapAt_bwd`), un-stripping along `c`, which has the
   module instances of `d` (`mods_configEq`);
5. the Core step is carried back by `Round7.step_unstrip`, and the new witness is again `RelE`
   (`stripConfig_mapConfig`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Runs

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.Reading (SStepB)
open Round4Int (BI)

variable {H : Type}

/-- Stripping after an export-only rewriting is stripping. -/
theorem stripConfig_mapConfig {μ : ModuleInst → ModuleInst} (hμ : ExportOnly μ) (e : Config H) :
    stripConfig (mapConfig μ e) = stripConfig e := by
  rw [← mapConfig_stripModule, mapConfig_comp, ← mapConfig_stripModule]
  exact congrArg (fun ν => mapConfig ν e) (funext hμ)

/-- `stripConfig` preserves `Bwd.ConfigEq`. -/
theorem configEq_strip {c d : Config H} (h : Bwd.ConfigEq c d) :
    Bwd.ConfigEq (stripConfig c) (stripConfig d) := by
  simpa only [mapConfig_stripModule] using configEq_map stripModule h

/-- **A `RelE` witness, stripped, is a round-6 `SimRel` witness of the stripped source.** -/
theorem simRel_strip {B : Builtins} {hn : H → String} {c d : Config H} (h : RelE B hn c d) :
    Round4.SimRel B hn (stripConfig c) (stripConfig d) :=
  ⟨configEq_strip h.1, h.2⟩

/-- **The two environments agree at an export-free image**, for an export-blind host. -/
theorem agree_strip {hn : H → String} {host : HostSemantics H} (hb : HostExportBlind host)
    (P : Profile) (d : Config H) (w : Value) :
    SStepB (utf8Env (BI P hn host)) (configV hn (stripConfig d)) w ↔
      SStepB (simEnv (BI P hn host)) (configV hn (stripConfig d)) w :=
  Determ.sStepB_utf8Env_iff (Determ.builtinsEF_BI P hn hb) (Round7.BI_utf8 P hn host)
    (ExpEnc.expFree_configV hn (noExports_strip d))

/-- Un-stripping a `RelE`-related pair keeps `RelE`. -/
theorem relE_unstrip {B : Builtins} {hn : H → String} {c c₀ d₂ : Config H}
    (h : Round4.SimRel B hn c₀ d₂) (hd : Stripped d₂) :
    RelE B hn (mapConfig (unstrip c) c₀) (mapConfig (unstrip c) d₂) := by
  refine ⟨configEq_map _ h.1, ?_⟩
  rw [stripConfig_mapConfig (exportOnly_unstrip c), hd]
  exact h.2

section
variable {hn : H → String} (hinj : Function.Injective hn) {host : HostSemantics H}
  (hf : HostFinite host) (hh : HostOk host) (hb : HostExportBlind host)
  (hp : HostExportParam host) {nd : Bool} {r : RelaxedChoice}
include hinj hf hh hb hp

/-- **The forward step along `RelE`**: a Core step of `c` that is its only successor is matched
from every `RelE` witness `d` by a step of the round-7 reading to a `RelE` witness of it. -/
theorem fwdRelE (c d c' : Config H) (ts : List CValType) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c d)
    (hs : Step (Profile.spec nd r) host c c')
    (hu : ∀ c₃, Step (Profile.spec nd r) host c c₃ → c₃ = c') :
    ∃ d', RelE (BI (Profile.spec nd r) hn host) hn c' d' ∧
      backendE.step (BI (Profile.spec nd r) hn host) (configV hn d) (configV hn d') := by
  obtain ⟨c₀, d₂, hs₀, hu₀, hr₂, hst⟩ :=
    Round6.Target.fwdRelR_of_open hinj hf hh (Round6.Int.openR_backend hinj hf hh)
      (stripConfig c) (stripConfig d) (stripConfig c') ts (configOk_strip hc)
      (boundedSel_strip hbc) (boundedSel_succ_strip hb hsucc) (simRel_strip hd)
      (step_strip hb hs)
  have hu' : ∀ c₃, Step (Profile.spec nd r) host (stripConfig c) c₃ → c₃ = stripConfig c' := by
    intro c₃ h₃
    obtain ⟨c₃', h₃', rfl⟩ := step_of_strip hb h₃
    rw [hu c₃' h₃']
  have hstr : Stripped d₂ :=
    stripped_of_configEq hr₂.1 (stripped_step hb hs₀ (stripped_stripConfig c))
  have hst₁ := (agree_strip hb (Profile.spec nd r) d _).mpr hst
  have hsub : ∀ m ∈ mods d, m ∈ mods c := fun m hm => mods_configEq hd.1 ▸ hm
  refine ⟨mapConfig (unstrip c) d₂, ?_,
    swapAt_fwd hinj hf hb hp _ hic hbc.2 hsub hstr hst₁⟩
  have hrel := relE_unstrip (c := c) hr₂ hstr
  rwa [hu₀ hu', unstrip_strip_succ hp hic hs hu] at hrel

/-- **The backward step along `RelE`**: a step of the round-7 reading from a `RelE` witness `d`
of `c` goes to a `RelE` witness of a Core successor of `c`. -/
theorem bwdRelE (c d : Config H) (ts : List CValType) (w : Value) (hc : ConfigOk c ts)
    (hbc : BoundedSelE c) (hic : StripInj c)
    (hsucc : ∀ c₁, Step (Profile.spec nd r) host c c₁ → BoundedSelE c₁)
    (hd : RelE (BI (Profile.spec nd r) hn host) hn c d)
    (hs : backendE.step (BI (Profile.spec nd r) hn host) (configV hn d) w) :
    ∃ c' d', RelE (BI (Profile.spec nd r) hn host) hn c' d' ∧ w = configV hn d' ∧
      Step (Profile.spec nd r) host c c' := by
  have hsub : ∀ m ∈ mods d, m ∈ mods c := fun m hm => mods_configEq hd.1 ▸ hm
  obtain ⟨w₀, hs₀, hw⟩ := swapAt_bwd hinj hf hb hp _ hic hbc.2 hsub hs
  have hs₁ := (agree_strip hb (Profile.spec nd r) d w₀).mp hs₀
  obtain ⟨c₀, d₂, hr₂, rfl, hst⟩ :=
    Round6.Target.bwdRelR_of_open hinj hf hh (Round5.BwdStep.growMaySucceed_spec nd r)
      (Round4.growMayFail_spec nd r) (Round6.Int.openR_backend hinj hf hh) (stripConfig c)
      (stripConfig d) ts _ (configOk_strip hc) (boundedSel_strip hbc)
      (boundedSel_succ_strip hb hsucc) (simRel_strip hd) hs₁
  have hstr : Stripped d₂ :=
    stripped_of_configEq hr₂.1 (stripped_step hb hst (stripped_stripConfig c))
  exact ⟨_, _, relE_unstrip hr₂ hstr, hw d₂ hstr rfl, step_unstrip hp hic hst⟩

end

end Silmaril.Wasm.SpecTec.Sim.Round7.Runs
