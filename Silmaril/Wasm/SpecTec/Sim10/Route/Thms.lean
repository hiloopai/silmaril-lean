module

public import Silmaril.Wasm.SpecTec.Sim10.Route.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10Good
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10Run
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Route10Store

/-!
# The 1.0 composite routes: what is proved

In `Silmaril.Wasm.SpecTec.Sim10` (proofs in `Sim10.Route10`):

* **`composite10 : Task.composite10`**: a V1 step goes through the copied 1.0 → Lime1 → 2.0
  simulation to a non-empty V2 run, and, under the 2.0 forward obligation `Fwd20` on the
  configurations that run visits, to a non-empty run of the corrected wasm-2.0 script
  (`Sim20.StepFix.simEnv20S`). This is conditional on `Fwd20`, which is proved only on fragments
  (`Sim20.Whole.wholeStepCtxS20` and siblings), as `Sim20.composite20` is conditional on Track E's
  obligation.
* **`composite10T : Task.composite10T`**: the same V2 run goes through the copied V2 → Core 3.0
  simulation and Round 6 to a non-empty run of the wasm-3.0 script (backend reading, Round 6's
  builtins `BI`), up to `Bwd.ConfigEq`, under `RunGood` at the Core image. No hypothesis on the 2.0
  side. It strengthens `Sim20.composite10_steps` (possibly empty runs) to one V1 step with a
  non-empty run.
* `transGen_fwd20`, `transGen_toCore`: the glue.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.composite10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.composite10

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.composite10T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.composite10T

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.fwd20_good20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.fwd20_good20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.composite10G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.composite10G

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.fwd20_good20C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.fwd20_good20C

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.runGood20_good20C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.runGood20_good20C

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.composite10C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.composite10C

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.not_fwd20_storeFn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.not_fwd20_storeFn

/-- info: 'Silmaril.Wasm.SpecTec.Sim10.not_fwd20_storeFnCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim10.not_fwd20_storeFnCfg
