module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30X
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XHandler
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XAll

/-!
# Existence of `Step_pure`/`Step_read` facts at `Wasm30.builtins`, by inversion: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdB30X`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdB30XTables,FwdB30XEngine,FwdB30XFlat,FwdB30XOk,`
`FwdB30XFam,FwdB30X,FwdB30XCtrl,FwdB30XHandler,FwdB30XAll}`; see `docs/projects/wasm-components.md`,
"Stretch, instfwd (ws4 an earlier step)".

At every evaluator `simEnv B` (no law of the primitives):

* `spure_of_sstep_flat`, `sread_of_sstep_flat`: a `Step` fact from `z; l`, where `l` is `k`
  values followed by one instruction named `t` (`FlatK k t l`), is `Step/pure` (`Step/read`) at
  the whole of `l`, when the decidable check `pureOk k t` (`readOk k t`) holds. The check reads
  the left-hand sides of the 218 rules of `Step`, `Step_pure` and `Step_read` through the tables
  `pureInfoT`, `readInfoT`, `stepInfoT`, which kernel `rfl` checks against the pinned script.

At the choice-made primitives `Wasm30.builtins`, the target of `Wasm30.toModel`:

* `pureX_builtins`, `pureX_two_sided`: at **every** `FwdX30.PureHeadX` redex (the numeric and
  vector families, `ref.i31`, `i31.get` and the primitive-free rules), on `DomDet`, a
  `Step_pure` fact of `stepModel builtins` exists to Core's successor up to `CfgRel`, and every
  such fact to typed code is that successor up to `CfgRel`.
* `readR_builtins`, `readR_two_sided`: the same for `Step_read` at `FwdB30.ReadG` redexes and
  at `ReadB` redexes (`ref.func`, the table, memory and aggregate reads).
* `readC_builtins`, `readC_two_sided`: the same at `ReadC` redexes (`block`, `loop`,
  `try_table`), whose value prefix has any length: there the shape of Core's successor (one
  label or handler, `cfgRel_single`) refutes `ctxt-instrs` instead of the forced lengths
  (`sread_of_sstep_single`).
* `readH_builtins`, `readH_two_sided`: the same at `ReadH` redexes (the `throw_ref` handler
  cases `catch`, `catch_ref`, `next`). The redex is one handler: the four `Step_pure` rules that
  name `HANDLER` are refuted by the constructors they force inside the body (`ruleInner`) or by
  `val*` (`not_fires_handlerVals`), and `ctxt-handler` by the successor's catch list.
* `readX_builtins`, `readX_two_sided`: hence at **every** `FwdX30.ReadHeadX` redex.

With `pureX_two_sided` and `readX_two_sided`, every classified head step of `FwdX30`
(`PureHeadX`, `ReadHeadX`) has its `Step_pure`/`Step_read` fact at `Wasm30.builtins`, two-sided
up to `CfgRel`, without any law of the choice-made primitives. Not covered: the cast rules
(`FwdX30Fin.CastRead`) and `return_call_ref` out of a frame at an address
(`FwdX30Fin.RetFrameAddr`), whose facts are known only at `Round4Int.BI`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.spure_of_sstep_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.spure_of_sstep_flat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.sread_of_sstep_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.sread_of_sstep_flat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.pureX_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.pureX_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.readR_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.readR_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.readC_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.readC_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30X.readX_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30X.readX_two_sided
