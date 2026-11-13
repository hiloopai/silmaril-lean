module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30

/-!
# The forward direction at the choice-made primitives `Wasm30.builtins`: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdB30`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdB30Ctrl,FwdB30}`; see `docs/projects/spectec/README.md`,
"insttyp".

* `spure_of_pureG`, `sread_of_readG`: the primitive-free rules of `PureHeadX`/`ReadHeadX`
  (`PureG`, `ReadG`) are `Step_pure`/`Step_read` facts in **every** evaluator `simEnv B`.
* `pureG_builtins`, `readG_builtins`: so on `DomDet` they are facts of `stepModel builtins`, the
  target of `Wasm30.toModel`, lifted to `Step` facts (existence, which `FwdX30Fin` left open).
* `pureG_two_sided`, `readG_two_sided`: with `FwdX30Fin`'s uniqueness, at these redexes the
  `Step_pure`/`Step_read` facts of `stepModel builtins` to typed code are exactly Core's successor
  up to `CfgRel`.

Not reached at `builtins`: the numeric and vector families, `ref.i31`, `i31.get` at a number,
`ref.func`, `block`, `loop`, `try_table`, three `throw_ref` handler cases, and the table, memory
and aggregate `Step_read` rules. Their leaves use laws of the primitives proved only at `BI`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30.pureG_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30.pureG_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30.readG_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30.readG_two_sided
