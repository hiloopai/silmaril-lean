module

public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Typing
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Convert
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Backward
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Concrete
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Findings

/-!
# SpecTec ↔ Core 3.0, float track: what is proved

* `Floats.floatTyping_simEnv B : Vec.FloatTyping (simEnv B)`, for every `B`: family V's typing
  interface for scalar floats and conversions (`numtype`, `num_(nt)` at every numeral, `num_(I32)`,
  `unop_`/`binop_`/`relop_` at `Fnn`, `cvtop__(nt_1, nt_2)` at every Core `ConvertOp`).
* `Floats.floatAgree_simEnv : FloatB P B → Vec.FloatAgree (simEnv B) P`: SpecTec's `$unop_`,
  `$binop_`, `$relop_` at `Fnn` and `$cvtop__` at every conversion, evaluated through the fixed
  script's own clauses, return exactly the result sets of Core's numerics under the profile `P`
  (every NaN payload `P` allows; the empty list exactly when a conversion traps), whenever the
  primitives of `B` extend `floatCall P` (`FloatB P B`).
* `Floats.floatIntB P`, a concrete interpretation of the primitives, with `Floats.intB_floatIntB`
  and `Floats.floatB_floatIntB`: the integer and the float facts hold together for one `B`.
* Backward, every number type: `Floats.bwd_unopVal`, `bwd_unopTrap` (never fires), `bwd_binopVal`,
  `bwd_binopTrap`, `bwd_relop`, `bwd_cvtopVal`, `bwd_cvtopTrap` (`Step_pure` 46–49, 51–53): a
  SpecTec step by the rule at the image of a Core sequence is the image of a Core step.
* Finding: `Floats.not_rFuns_unrestricted B`: round 1's `RefsGC.RFuns` quantified a call over
  every scope, including one redirecting the called name, and so held in no `simEnv B` (which made
  round 1's `Whole.Assumptions` unsatisfiable). `RefsGC.RFuns` is now restricted to term-only
  scopes (`ValsOnly`), and `Floats.rFunsVals_of_floatB` proves it for every `B` with `FloatB P B`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.floatTyping_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.floatTyping_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.floatAgree_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.floatAgree_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.intB_floatIntB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.intB_floatIntB

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.bwd_cvtopVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.bwd_cvtopVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.bwd_binopVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.bwd_binopVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.not_rFuns_unrestricted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.not_rFuns_unrestricted

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Floats.rFunsVals_of_floatB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Floats.rFunsVals_of_floatB
