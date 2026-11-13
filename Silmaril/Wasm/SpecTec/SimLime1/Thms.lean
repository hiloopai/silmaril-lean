module

public import Silmaril.Proofs.Wasm.SpecTec.SimLime1.Route

/-!
# Lime1 against the SpecTec scripts

Lime1 has no SpecTec script of its own: it is a profile (`Silmaril.Wasm.Models.lime1`) of the Wasm
specification, with `lime1 ≤ v30` and `¬ lime1 ≤ v20` (extended constants arrived in 3.0). Its
execution reaches the scripts through the copied simulations, as the 1.0 routes do
(`Sim10.composite10T`, `Sim10.composite10`). In `Silmaril.Proofs.Wasm.SpecTec.SimLime1`:

* **`compositeL1T`**: Lime1 → Core 3.0 → the **wasm-3.0 script**. A Lime1 step from a
  configuration simulated by a Core configuration that only reaches good configurations
  (`Sim20.RunGood`) is matched, up to `Bwd.ConfigEq`, by a non-empty run of wasm-3.0 backend
  steps at Round 6's builtins `BI`. No hypothesis on the Lime1 side;
* `compositeL1_steps`: the same for Lime1 runs, with a possibly empty run of the script;
* **`compositeL1`**: Lime1 → 2.0 → the corrected **wasm-2.0 script**, conditional on the 2.0
  forward obligation `Sim10.Fwd20` (as `Sim10.composite10`). Lime1 code runs in 2.0 even though
  a Lime1 module with an extended constant is not a 2.0 module: constant expressions are
  evaluated at instantiation, so they never reach the step relation.

The 1.0 script is not a target: Lime1 instructions outside 1.0 (sign extension, saturating
conversions, multi-value blocks, `memory.copy`/`memory.fill`) have no rule there.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1T

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1_steps

/-- info: 'Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Proofs.Wasm.SpecTec.SimLime1.compositeL1
