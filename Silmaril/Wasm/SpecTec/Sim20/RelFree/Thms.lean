module

public import Silmaril.Wasm.SpecTec.Sim20.RelFree.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFreeEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20Check
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20Rules
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.RelFree20

/-!
# Relation-free syntax: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.RelFree`; see `docs/projects/spectec/README.md`.

* `agreeAt`, `tAgreeAt` (unrefined, `Raw/…/Sim20/RelFree/{Eval,Typ}.lean`): at every fuel, the
  evaluator and the typing block answer in `withRels env R` at least what they answer in `env`, on
  relation-free syntax, when the definitions of `env` outside `bad` and all its types are
  relation-free. The proofs follow round 7's `Round7.Script.agreeAt` and
  `Round7.TypAgree.tAgreeAt_succ`, with `derives` dropped from the induction.
* `evalExp_withRels_iff`, `hasTyp_withRels_iff`, `ruleBody_withRels` (`RelFreeEq`): the same as
  statements about `EvalExp`, `HasTyp` and rule bodies.
* `defsOkB_fixed20`, `typsOkB_fixed20`, `stepRules20_spec` (kernel), `defsGood_simEnv20`,
  `typsGood_simEnv20`, `simEnv20S_eq` (`RelFree20`): the 2.0 instance, with
  `bad20 = ["instantiate"]`.
* `otherwiseAt_withRels_iff`, `fires_withRels_iff` (`RelFreeEq`): `otherwise` and the firings of a
  relation with relation-free rules agree under any relation table; `spure20S_iff`,
  `sread20S_iff` (`RelFree20`, with the kernel checks `pureRules20_spec`, `readRules20_spec`):
  `Step_pure` and `Step_read` derive alike in `simEnv20 B` and `simEnv20S B`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.ruleBody_withRels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.ruleBody_withRels

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.hasTyp_withRels_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.hasTyp_withRels_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.evalExp_withRels_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.evalExp_withRels_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.simEnv20S_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.simEnv20S_eq

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.defsGood_simEnv20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.defsGood_simEnv20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.typsGood_simEnv20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.typsGood_simEnv20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.stepRules20_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.stepRules20_spec

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.spure20S_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.spure20S_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.sread20S_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.sread20S_iff

/--
info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.otherwiseAt_withRels_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.otherwiseAt_withRels_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.RelFree.fires_withRels_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.RelFree.fires_withRels_iff
