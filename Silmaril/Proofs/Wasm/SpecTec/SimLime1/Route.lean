module

public import Silmaril.Wasm.SpecTec.Sim10.Route.Thms

/-!
# Lime1 against the SpecTec scripts: the composite routes

There is no SpecTec script of Lime1 itself: Lime1 is a profile, a feature set over the Wasm
specification (`Silmaril.Wasm.Models.lime1`, with `lime1 ≤ v30` and `¬ lime1 ≤ v20`). Its
execution is related to the scripts through the copied simulations, as the 1.0 routes are
(`Sim10.composite10`, `Sim10.composite10T`):

* **`compositeL1T`**, Lime1 → Core 3.0 → the **wasm-3.0 script**: a Lime1 step from a
  configuration simulated (`Lime1.Execution.Sim`) by a Core configuration that only reaches good
  configurations (`Sim20.RunGood`) is matched, up to `Bwd.ConfigEq`, by a non-empty run of
  wasm-3.0 backend steps at Round 6's builtins `BI`. The Core run is the copied
  `Lime1.Execution.Step.toCore` (one or more Core steps); `Sim20.stepsT_sim` follows it, one
  reading step per Core step. No hypothesis on the Lime1 side;
* `compositeL1_steps`: the same for Lime1 runs (`Lime1.Execution.Steps.toCore`, Round 6's
  `runsR_backend`), with a possibly empty run of the script;
* **`compositeL1`**, Lime1 → 2.0 → the corrected **wasm-2.0 script**, given the 2.0 forward
  obligation `Sim10.Fwd20` on the configurations the 2.0 run visits (as `Sim10.composite10`). The
  copied `Lime1.Execution.Step.toV2` goes through 2.0 at `v2Profile = Profile.spec`. Lime1 code
  runs in 2.0 although Lime1 modules need not be 2.0 modules: extended constants are evaluated at
  instantiation, so no extended-constant expression reaches the 2.0 step relation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SpecTec.SimLime1

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim (HostFinite)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.Round4 (SimRel)
open Silmaril.Wasm.SpecTec.Sim.Round4Int (BI)

variable {H : Type}

/-- **Lime1 → Core 3.0 → the wasm-3.0 script, with a non-empty run**, at Round 6's builtins. -/
theorem compositeL1T (hn : H → String) (hinj : Function.Injective hn)
    (host : Execution.Core.HostSemantics H) (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) (src : Lime1.Execution.HostSemantics H)
    (hosts : Lime1.Execution.HostCompatible src host)
    {a b : Lime1.Execution.Config H} {c : Execution.Core.Config H}
    (hab : Lime1.Execution.Step src a b) (hs : Lime1.Execution.Sim a c)
    (hgood : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    ∃ c' d, Lime1.Execution.Sim b c' ∧ Silmaril.Wasm.SpecTec.Sim.Bwd.ConfigEq c' d ∧
      Relation.TransGen (Silmaril.Wasm.SpecTec.Sim.Round6.Int.backend.step (BI Profile.spec hn host))
        (Silmaril.Wasm.SpecTec.Sim.configV hn c) (Silmaril.Wasm.SpecTec.Sim.configV hn d) := by
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := Silmaril.Wasm.SpecTec.Sim20.runGood_parts hgood
  obtain ⟨c', hcc, hs'⟩ := Lime1.Execution.Step.toCore hosts hab hs
  have h₀ : SimRel (BI Profile.spec hn host) hn c c :=
    ⟨Silmaril.Wasm.SpecTec.Sim.Bwd.ConfigEq.refl _,
      Silmaril.Wasm.SpecTec.Sim.Round5.Target.typed_of_configOk_sel _ hn hok (hb _ .refl)⟩
  obtain ⟨d, hr, hT⟩ := Silmaril.Wasm.SpecTec.Sim20.stepsT_sim hinj hf hh
    (Silmaril.Wasm.SpecTec.Sim.Round6.Int.openR_backend hinj hf hh) hok hb h₀
    (Silmaril.Wasm.SpecTec.Sim20.detTrans_of_trans hcc hd)
  exact ⟨c', d, hs', hr.1, hT⟩

/-- **Lime1 runs, through Core 3.0, then the wasm-3.0 script**: a (possibly empty) Lime1 run is a
Core run (`Lime1.Execution.Steps.toCore`), and wasm-3.0 backend steps reach the encoding of a
`ConfigEq`-twin of its end. -/
theorem compositeL1_steps (hn : H → String) (hinj : Function.Injective hn)
    (host : Execution.Core.HostSemantics H) (hf : HostFinite host)
    (hh : Execution.Core.HostOk host) (src : Lime1.Execution.HostSemantics H)
    (hosts : Lime1.Execution.HostCompatible src host)
    {a b : Lime1.Execution.Config H} {c : Execution.Core.Config H}
    (hab : Lime1.Execution.Steps src a b) (hs : Lime1.Execution.Sim a c)
    (hgood : Silmaril.Wasm.SpecTec.Sim20.RunGood Profile.spec host c) :
    ∃ c' d, Lime1.Execution.Sim b c' ∧ Execution.Core.Steps Profile.spec host c c' ∧
      Silmaril.Wasm.SpecTec.Sim.Bwd.ConfigEq c' d ∧
      Silmaril.Wasm.SpecTec.Sim.Round6.Target.RSteps Silmaril.Wasm.SpecTec.Sim.Round6.Int.backend
        (BI Profile.spec hn host) (Silmaril.Wasm.SpecTec.Sim.configV hn c)
        (Silmaril.Wasm.SpecTec.Sim.configV hn d) := by
  obtain ⟨⟨ts, hok⟩, hb, hd⟩ := Silmaril.Wasm.SpecTec.Sim20.runGood_parts hgood
  obtain ⟨c', ht, hs'⟩ := Lime1.Execution.Steps.toCore hosts hab hs
  obtain ⟨d, hEq, hR⟩ := (Silmaril.Wasm.SpecTec.Sim.Round6.Int.runsR_backend hinj hf hh).1 _ _ ts
    hok hb (Silmaril.Wasm.SpecTec.Sim20.detSteps_of_steps ht hd)
  exact ⟨c', d, hs', ht, hEq, hR⟩

/-- **Lime1 → 2.0 → the corrected wasm-2.0 script**, given the 2.0 forward obligation on the
configurations the 2.0 run visits. -/
theorem compositeL1 (hn : H → String) (src : Lime1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H) (B : Builtins) (Good : V2.Execution.Config H → Prop)
    (hosts : Lime1.Execution.ToV2.HostCompatible src tgt)
    (hF : Silmaril.Wasm.SpecTec.Sim10.Fwd20 hn tgt B Good)
    {a b : Lime1.Execution.Config H} {c : V2.Execution.Config H}
    (hab : Lime1.Execution.Step src a b) (hs : Lime1.Execution.ToV2.Sim a c)
    (hg : Silmaril.Wasm.SpecTec.Sim10.RunGood20 tgt Good c) :
    ∃ c', Lime1.Execution.ToV2.Sim b c' ∧
      Relation.TransGen (SStepB (Silmaril.Wasm.SpecTec.Sim20.StepFix.simEnv20S B))
        (Silmaril.Wasm.SpecTec.Sim20.configV hn c) (Silmaril.Wasm.SpecTec.Sim20.configV hn c') := by
  obtain ⟨c', hcc, hs'⟩ := Lime1.Execution.Step.toV2 hosts hab hs
  exact ⟨c', hs', Silmaril.Wasm.SpecTec.Sim10.transGen_fwd20 hF hcc hg⟩

end Silmaril.Proofs.Wasm.SpecTec.SimLime1
