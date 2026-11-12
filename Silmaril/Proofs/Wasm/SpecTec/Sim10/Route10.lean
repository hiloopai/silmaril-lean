module

public import Silmaril.Wasm.SpecTec.Sim10.Route.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RouteT

/-!
# The 1.0 composite routes, proved

* `transGen_fwd20`: a non-empty run of V2 steps from a configuration all of whose successors are
  good is a non-empty run of the corrected wasm-2.0 script, under `Fwd20`;
* **`composite10 : Task.composite10`**: V1's step goes to a non-empty V2 run
  (`V1.Execution.Step.toV2`), and that run goes to the 2.0 script;
* `transGen_toCore`: a non-empty run of V2 steps along `V2.Execution.Sim` is a non-empty Core run
  (`V2.Execution.Step.toCore`, step by step);
* **`composite10T : Task.composite10T`**, at Round 6's builtins `BI`: the Core run is
  deterministic under `RunGood` (`Sim20.detTrans_of_trans`), so Round 6 follows it one reading
  step per Core step (`Sim20.stepsT_sim`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round4 (SimRel)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)

variable {H : Type}

/-- **A non-empty V2 run from a configuration whose successors are good is a non-empty run of
the corrected 2.0 script**, under `Fwd20`. -/
theorem transGen_fwd20 {hn : H → String} {tgt : V2.Execution.HostSemantics H} {B : Builtins}
    {Good : V2.Execution.Config H → Prop} (hF : Fwd20 hn tgt B Good) {c c' : V2.Execution.Config H}
    (h : Relation.TransGen (V2.Execution.Step v2Profile tgt) c c') (hg : RunGood20 tgt Good c) :
    Relation.TransGen (SStepB (Sim20.StepFix.simEnv20S B)) (Sim20.configV hn c)
      (Sim20.configV hn c') := by
  induction h with
  | single h => exact hF _ _ (hg _ .refl) h
  | @tail c₁ c₂ h₁ h₂ ih =>
    have hg₁ : Good c₁ := hg c₁ h₁.to_reflTransGen
    exact ih.trans (hF _ _ hg₁ h₂)

/-- **`Task.composite10` holds**: 1.0 → 2.0 → the corrected 2.0 script, given the 2.0 forward
obligation on the configurations the V2 run visits. -/
theorem composite10 : Task.composite10 := by
  intro H hn src tgt B Good hosts hF a b c hab hs hg
  obtain ⟨c', hcc, hs'⟩ := V1.Execution.Step.toV2 hosts hab hs
  exact ⟨c', hs', transGen_fwd20 hF hcc hg⟩

/-- **A non-empty V2 run along `V2.Execution.Sim` is a non-empty Core run.** -/
theorem transGen_toCore {P : Profile} {src : V2.Execution.HostSemantics H}
    {host : Execution.Core.HostSemantics H} (hosts : V2.Execution.HostCompatible src host)
    {e e' : V2.Execution.Config H} {c : Execution.Core.Config H}
    (h : Relation.TransGen (V2.Execution.Step P src) e e') (hs : V2.Execution.Sim e c) :
    ∃ c', Relation.TransGen (Execution.Core.Step P host) c c' ∧ V2.Execution.Sim e' c' := by
  induction h generalizing c with
  | single h => exact V2.Execution.Step.toCore hosts h hs
  | tail _ h₂ ih =>
    obtain ⟨c₁, hc₁, hs₁⟩ := ih hs
    obtain ⟨c₂, hc₂, hs₂⟩ := V2.Execution.Step.toCore hosts h₂ hs₁
    exact ⟨c₂, hc₁.trans hc₂, hs₂⟩

/-- **`Task.composite10T` holds**, at Round 6's builtins `BI`: 1.0 → 2.0 → Core 3.0 → the
wasm-3.0 script, with a non-empty run. -/
theorem composite10T : Task.composite10T := by
  intro H hn hinj host hf hh src tgt hosts₁ hosts₂
  refine ⟨BI Profile.spec hn host, fun a b e c hab he hs hgood => ?_⟩
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := Sim20.runGood_parts hgood
  obtain ⟨e', hee, he'⟩ := V1.Execution.Step.toV2 hosts₁ hab he
  obtain ⟨c', hcc, hs'⟩ := transGen_toCore hosts₂ hee hs
  have h₀ : SimRel (BI Profile.spec hn host) hn c c :=
    ⟨Sim.Bwd.ConfigEq.refl _, Sim.Round5.Target.typed_of_configOk_sel _ hn hok (hb _ .refl)⟩
  obtain ⟨d, hr, hT⟩ := Sim20.stepsT_sim hinj hf hh (Sim.Round6.Int.openR_backend hinj hf hh) hok
    hb h₀ (Sim20.detTrans_of_trans hcc hd)
  exact ⟨e', c', d, he', hs', hr.1, hT⟩

end Silmaril.Wasm.SpecTec.Sim10
