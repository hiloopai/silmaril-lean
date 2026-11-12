module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Int3.Assemble

/-!
# SpecTec ↔ Core 3.0, round 5, pass-3 integration: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Int3`; see `docs/projects/spectec/README.md`.

* `open2_of_open4`, `open4_of_open2`: pass 2's `Round5.Int2.Open2` is `Open4` plus the four
  leaves pass 3 proved (`hostRespects`, `read`, `vtestop`, `vector`).
* `wholeStepValidOk_of_open4`, `multiOk2_of_open4`, `runs_of_open4`: the restated target and the
  run corollaries from `Open4`.
* `not_open4`, `not_open4_spec`: `Open4` is unsatisfiable (`simd` always; `vecOps` under the spec
  NaN profile), so the results above are vacuous as stated.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.open2_of_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.open2_of_open4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.not_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.not_open4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.not_open4_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.not_open4_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.wholeStepValidOk_of_open4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.wholeStepValidOk_of_open4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.multiOk2_of_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.multiOk2_of_open4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Int3.runs_of_open4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Int3.runs_of_open4
