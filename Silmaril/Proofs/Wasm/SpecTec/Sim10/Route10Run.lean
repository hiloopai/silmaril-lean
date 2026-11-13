module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10
public import Silmaril.Wasm.SpecTec.Sim20.Whole.Thms

/-!
# The 1.0 → 2.0-script composite from a single covered configuration

`Task.composite10G` assumes that the whole V2 run stays in `Good20S`
(`RunGood20 tgt (Good20S …) c`), a hypothesis on every reachable configuration. An earlier step
replaces it by a hypothesis on the starting configuration alone: `Sim20.Whole.Good20C`, which
is preserved by every V2 step and on which every V2 step is matched forward
(`Sim20.Whole.fwd_good20C`, `good20C_steps`).

* `fwd20_good20C`, `runGood20_good20C`: `Fwd20` holds on `Good20C` at `storeB v2Profile`, and
  `RunGood20 tgt (Good20C …) c` follows from `Good20C … c`;
* **`Task.composite10C`** (stated and proved, `composite10C`): every V1 step from a configuration
  simulated by a covered V2 configuration is matched by a non-empty run of the corrected
  wasm-2.0 script at `storeB v2Profile`, with no hypothesis on the rest of the run.

What `Good20C` still asks is stated, not discharged: a typed image with whole pages, and code and
store functions inside the covered instruction set (control, scalar numeric, references,
variables, unpacked loads; no tables, stores, packed loads, other memory instructions, vectors,
`call_indirect` or host functions). At an invocation
`val* (CALL_ADDR a)` only the typed image, whole pages and the store condition remain
(`Sim20.Whole.good20C_invoke`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Lime1.Execution (v2Profile)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **The 2.0 forward obligation holds on `Good20C`**, at `storeB v2Profile`. -/
theorem fwd20_good20C {H : Type} (hn : H → String) (host : V2.Execution.HostSemantics H) :
    Fwd20 hn host (Sim20.Whole.storeB v2Profile) (Sim20.Whole.Good20C hn v2Profile) :=
  fun _ _ hg h => .single (Sim20.Whole.fwd_good20C hg h).2

/-- **A covered configuration only reaches covered configurations.** -/
theorem runGood20_good20C {H : Type} {hn : H → String} {host : V2.Execution.HostSemantics H}
    {c : V2.Execution.Config H} (hg : Sim20.Whole.Good20C hn v2Profile c) :
    RunGood20 host (Sim20.Whole.Good20C hn v2Profile) c :=
  fun _ h => Sim20.Whole.good20C_steps h hg

/-- **The 1.0 → 2.0-script composite from a covered configuration** (stated and proved). -/
def Task.composite10C : Prop :=
  ∀ (H : Type) (hn : H → String) (src : V1.Execution.HostSemantics H)
    (tgt : V2.Execution.HostSemantics H),
    Lime1.Execution.ToV2.HostCompatible (src.mapCode V1.Func.toLime) tgt →
    ∀ (a b : V1.Execution.Config H) (c : V2.Execution.Config H), V1.Execution.Step src a b →
      Lime1.Execution.ToV2.Sim a.toLime c → Sim20.Whole.Good20C hn v2Profile c →
      ∃ c', Lime1.Execution.ToV2.Sim b.toLime c' ∧
        Relation.TransGen (SStepB (Sim20.StepFix.simEnv20S (Sim20.Whole.storeB v2Profile)))
          (Sim20.configV hn c) (Sim20.configV hn c')

/-- **`Task.composite10C` is proved**, from `composite10`, `fwd20_good20C` and
`runGood20_good20C`. -/
theorem composite10C : Task.composite10C := fun H hn src tgt hosts a b c hab hs hg =>
  composite10 H hn src tgt _ _ hosts (fwd20_good20C hn tgt) a b c hab hs (runGood20_good20C hg)

end Silmaril.Wasm.SpecTec.Sim10
