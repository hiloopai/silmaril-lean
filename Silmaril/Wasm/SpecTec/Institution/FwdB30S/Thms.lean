module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30S.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SExact
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SStep
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SCast
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SFrame
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SRigid
public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30SRigidR

/-!
# `Step` facts at `Wasm30.builtins` beyond `FwdB30X`: results

Namespace `Silmaril.Wasm.SpecTec.Institution.FwdB30S`; proofs in
`Silmaril.Proofs.Wasm.SpecTec.Institution.{FwdB30SExact,FwdB30SStep,FwdB30SCast,FwdB30SFrame,`
`FwdB30SRigid,FwdB30SRigidR}`; see `docs/projects/spectec/README.md`, "instfwd".

All results are at the choice-made primitives `Wasm30.builtins` (the target of
`Wasm30.toModel`), on `DomDet`, and use no law of those primitives: the only knowledge of
`builtins` is `FwdX30Fin.stepObs_builtins` (Core's successor is a `Step` fact up to `CfgRel`),
and the rest is inversion of `Step` derivations at an arbitrary `B`.

* **Beyond `CfgRel`.** `cfgRel_exact`: `CfgRel` from the image of a configuration whose code has
  no `CALL_REF`, label, handler or frame at the top (`RigidV`) is equality. Hence
  `pureX_exact` (every `FwdX30.PureHeadX` redex), `readB_exact` (`ref.func`, the table, memory
  and aggregate reads), `readX_exact` (every `ReadHeadX` redex with a rigid successor),
  `castRead_exact` and `storeW_exact`: the fact is to the image of Core's successor itself.
* **The casts.** `sreadB_of_sstepB_pair`: under the backend reading, at every `simEnv B`, a
  `Step` fact from `[ref r, cast]` is `Step/read` at the pair. `castRead_builtins`,
  `castRead_two_sided`: the eight cast rules (`FwdX30Fin.CastRead`) have their `Step_read`
  facts, two-sided up to `CfgRel`.
* **`return_call_ref` out of a frame at an address.** `sread_of_sstep_frame`: at every
  `simEnv B`, a `Step` fact from the frame that is not one instruction is `Step/read`.
  `retFrameAddr_builtins`, `retFrameAddr_two_sided`: `FwdX30Fin.RetFrameAddr` has its
  `Step_read` fact, two-sided up to `CfgRel` (not exact: Core resolves the `CALL_REF`
  annotation, SpecTec keeps it).
* **Store-changing `Step` rules.** `sstep_head_flat`: at a checked flat redex (`stepOk`), a
  `Step` fact is a rule of `Step` from rule 6 on, fired at the whole redex. `storeW_builtins`,
  `storeW_two_sided`, `storeW_exact`: at every `StoreW` redex (`local.set`, `global.set`,
  `table.set`, `table.grow`, `elem.drop`, the stores, `memory.grow`, `data.drop`, `struct.set`,
  `array.set`), such a rule fires (under `stepModel`'s reading) with the image of Core's
  successor as its conclusion, and that is the only `Step` fact there.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Institution

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.cfgRel_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.cfgRel_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.pureX_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.pureX_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.readB_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.readB_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.sreadB_of_sstepB_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.sreadB_of_sstepB_pair

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.castRead_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.castRead_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.castRead_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.castRead_exact

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.sread_of_sstep_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.sread_of_sstep_frame

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.retFrameAddr_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.retFrameAddr_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.sstep_head_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.sstep_head_flat

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.storeW_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.storeW_two_sided

/-- info: 'Silmaril.Wasm.SpecTec.Institution.FwdB30S.storeW_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FwdB30S.storeW_exact
