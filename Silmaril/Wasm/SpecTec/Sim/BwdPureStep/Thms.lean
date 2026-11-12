module

public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Dispatch

/-!
# SpecTec ↔ Core 3.0, round 3, track bwd-pure-step: what is proved

Backward lemmas (SpecTec → Core: whatever the rule derives from the image of a configuration
is the image of a Core step), at every `simEnv B`:

* `Step_pure` 31–45 (`BwdPureStep.pure_done`): `ref.i31`, `ref.is_null`, `ref.as_non_null`,
  `ref.eq`, `i31.get`, `array.new`, `extern.convert_any`, `any.convert_extern`;
* `Step` 11–14, 17, 18, 20, 28, 30, 33, 34 (`BwdPureStep.step_done`): `local.set`, `global.set`,
  `table.set`, `store-num-oob`, `store-pack-oob`,
  `elem.drop`, `data.drop`, `struct.set-null`, `array.set-null`, `array.set-oob`;

under `BwdB B` (`$wrap__`/`$extend__` are Core's; `B` does not interpret the four store
updaters, `$table` and `$mem`), which holds for the concrete `Prims.builtins` (`BwdPureStep.bwdB_builtins`).
`Integrate.RemainingW` no longer lists these rules.
-/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdPureStep.pure_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BwdPureStep.pure_done

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdPureStep.step_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BwdPureStep.step_done

/-- info: 'Silmaril.Wasm.SpecTec.Sim.BwdPureStep.bwdB_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BwdPureStep.bwdB_builtins
