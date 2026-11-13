module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The 1.0 → 2.0-script composite without a `Fwd20` hypothesis, on covered runs

`Task.composite10` takes the 2.0 forward obligation `Fwd20` on a set `Good` as a hypothesis. Round 3
An earlier step proves it on `Sim20.Whole.Good20S` at the builtins `Sim20.Whole.storeB v2Profile`
(`fwd20_good20S`): the configurations whose every V2 step is either in the nested forward fragment
(from a typed image with whole pages) or a top-level scalar store (from a typed state). So:

* **`Task.composite10G`** (stated and proved, `composite10G`): every V1 step from a configuration
  simulated by a V2 configuration whose run stays in `Good20S` is matched by a non-empty run of the
  corrected wasm-2.0 script at `storeB v2Profile`, with no `Fwd20` hypothesis.

What is still conditional is the coverage itself: `RunGood20 tgt (Good20S …)` is a hypothesis on
the run. It fails at configurations that step by a rule outside both fragments (`block`, `loop`,
calls through `call_indirect` or to a function address, table and memory reads, the vector
operators, host calls, and stores below the top of the code).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **The 2.0 forward obligation holds on `Good20S`**, at `storeB v2Profile`. -/
theorem fwd20_good20S {H : Type} (hn : H → String) (host : V2.Execution.HostSemantics H) :
    Fwd20 hn host (Sim20.Whole.storeB v2Profile) (Sim20.Whole.Good20S hn v2Profile host) :=
  fun _ _ hg h => .single (Sim20.Whole.fwd_good20S hg h)

/-- **The 1.0 → 2.0-script composite on covered runs** (stated and proved): every V1 step from a
configuration simulated by a V2 configuration whose whole run stays in `Good20S` is matched by a
non-empty run of the corrected wasm-2.0 script at `storeB v2Profile`, ending at a V2
configuration that simulates the V1 successor. -/
def Task.composite10G : Prop :=
  ∀ (H : Type) (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H),
    Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt →
    ∀ (a b : V1.Execution.Config H) (c : V2.Execution.Config H), V1.Execution.Step src a b →
      Lime1.Execution.ToV2.Sim a.toLime c →
      RunGood20 tgt (Sim20.Whole.Good20S hn v2Profile tgt) c →
      ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
        Relation.TransGen (SStepB (Sim20.StepFix.simEnv20S (Sim20.Whole.storeB v2Profile)))
          (Sim20.configV hn c) (Sim20.configV hn c')

/-- **`Task.composite10G` is proved**, from `composite10` and `fwd20_good20S`. -/
theorem composite10G : Task.composite10G := fun H hn src tgt hosts a b c hab hs hg =>
  composite10 H hn src tgt _ _ hosts (fwd20_good20S hn tgt) a b c hab hs hg

end Silmaril.Wasm.SpecTec.Sim10
