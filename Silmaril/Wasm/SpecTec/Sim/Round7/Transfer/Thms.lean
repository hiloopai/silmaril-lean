module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Transfer.Move

/-!
# SpecTec ↔ Core 3.0, round 7: derivations with `ExpFree` quantifiers move to `simEnv B`

The non-monotone direction of `Round7.Task.envAgreeNE`, for positive derivations, reduced to
determination:

* `relRulesOk_fixed` (kernel, `decide +kernel`): every relation `Step` reaches has no
  parameters, and its rules' conclusion alternatives and premises are harmless;
* `dderivesB_simEnv_of_E`: a `DDerivesBE (utf8Env B) O` derivation (one whose rule instances
  bind every quantifier to an `ExpFree` value) of a reachable relation is a
  `DDerivesB (simEnv B) O'` derivation, for `O ≤ O'` and `B` leaving `$utf8` uninterpreted
  (round 6's `BI`, `Round7.BI_utf8`);
* `sStepB_simEnv_of_E`: the same for `Step` read with `otherwiseB`, given that `otherwiseB` in
  `utf8Env B` implies `otherwiseB` in `simEnv B`; `dderivesB_noElse_simEnv_of_E` for `noElse`.

Still open for `Task.envAgreeNE`: that every `utf8Env B` derivation of `Step` from round 6's
domain is a `DDerivesBE` derivation (determination), and the two inclusions between the
`otherwiseB` readings.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Transfer

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.relRulesOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relRulesOk_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.dderivesB_simEnv_of_E' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_simEnv_of_E

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.sStepB_simEnv_of_E' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_simEnv_of_E

end Silmaril.Wasm.SpecTec.Sim.Round7.Transfer
