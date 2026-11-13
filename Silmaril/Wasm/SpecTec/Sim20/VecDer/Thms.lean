module

public import Silmaril.Wasm.SpecTec.Sim20.VecDer.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerEnv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerMove
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerElse
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerPairs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerTask
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerPat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerCensus
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerBind
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecDerLift

/-!
# Derivations across the 2.0 vector type errata: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecDer`; see `docs/projects/spectec/README.md`, "vec".
This is the type-errata half of the transfer `simEnv20T (storeB P)` → `simEnv20V (vecNB P)`:
`simEnv20T B` → `simEnv20V B` at the same builtins.

* `VecDerEnv`: `envSameTV` (the two evaluate alike); `typsOffB_vbad20` (kernel: `vbad20`, round
  4's `tbad20` plus the three families, is closed); **`hasTyp_offV_iff`** (off `vbad20`, typing
  is the same in both directions); **`quantsOk_toV`** (harmless quantifiers, `QuantsV`, move
  forward).
* `VecDerMove`: `DDerivesBS S` (derivations with a side condition at every rule instance);
  **`dderivesBS_move`**, generic in an `EnvSame` pair; `dderivesBS_toV` under `ElseMoveS`.
* `VecDerElse`: **`otherwiseAtB_sym`**: `otherwise` agrees in two environments that evaluate
  alike, at a rule typed in both, when every `otherwise` rule types its earlier rules alike
  (`PairSym`). Typing does not grow across the family erratum, so earlier rules are read in both
  directions.
* `VecDerPairs`, `VecDerTask`: the pair check `pairOkV` and its soundness; the kernel runs it on
  `Step_read` and `Step_pure` (`readPairsV`, `purePairsV`). **`else_iffV`**, **`elseMoveV`**,
  **`dderivesBS_toV'`**, **`sstepBS_toV'`**: every derivation of `simEnv20T B` with harmless
  quantifiers is one of `simEnv20V B`.
* `VecDerPat`, `VecDerCensus`: **`vOk_of_patB`** (a variable at a pattern position of a `VOk`
  value is `VOk`); the kernel census (`census_step`, `census_pure`, `census_read`,
  `patOk_fails`): every rule of the three relations reads `QuantsV` off a `VOk` conclusion except
  exactly six (`patExcl`: `Step_pure` 34–37, 40, the operator-family rules, and `Step_read` 5,
  `call_addr`); **`quantsV_of_rule`**.
* `VecDerBind`, `VecDerLift`: `vOk_of_bldB` and the premise census (`premCensus_*`);
  **`toSideV`**, **`dderivesBN_toV`**, **`sstepBN_toV`**: a `Step` of `simEnv20T B` between `VOk`
  configurations that uses none of the six rules is a `Step` of `simEnv20V B`.

Not covered here: the builtins half (`storeB P` → `vecNB P`), derivations that use `call_addr`
or a family rule, and the old (`SStep`) reading that `VecWhole.FwdBaseV` uses.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.typsOffB_vbad20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.typsOffB_vbad20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.hasTyp_offV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.hasTyp_offV_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.dderivesBS_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.dderivesBS_move

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.otherwiseAtB_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.otherwiseAtB_sym

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.elseMoveV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.elseMoveV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.sstepBS_toV'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.sstepBS_toV'

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.vOk_of_patB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.vOk_of_patB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.patOk_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.patOk_fails

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.quantsV_of_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.quantsV_of_rule

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.toSideV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.toSideV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecDer.sstepBN_toV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecDer.sstepBN_toV
