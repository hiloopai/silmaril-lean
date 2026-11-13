module

public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.BridgeInstantiation
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Lime1.Binary

/-!
# Agreement of the Wasm 1.0, Lime1 and Core 3.0 binary grammars

The header of a hand copy of old silmaril's binary agreement
(an earlier development, `Silmaril/Wasm/Binary/{V1Lime1,Lime1Core,Agreement,Bridge,
BridgeInstantiation}.lean`, `Silmaril/Wasm/Lime1/{ToV1,Validation/Aligns}.lean`; provenance in
(`Silmaril/Raw/Wasm/SpecTec/Wasm/Lime1/Binary/*`). The grammars are relations
`Bytes → Module → Prop`, each functional. The main facts, all in namespace
`Silmaril.Wasm.Binary` unless noted:

* `v1_iff_lime1`, `v1_lime1`: 1.0 bytes are Lime1 bytes of `m.toLime`, exactly the Lime1
  bytes without call-indirect-overlong;
* `lime1_core`, `lime1_iff_core_forms`: Lime1 bytes of a binary-compatible module are Core 3.0
  bytes of `m.toCoreBinary`, exactly the Core bytes with Lime1's gated forms and numeric
  locals; `Lime1.Validation.ModuleValid.binaryCompat`: valid modules are compatible;
* `lime1_core_toCore_counterexample`: with an element segment, Core does **not** decode the
  bytes to `m.toCore` (the legacy segment form decodes to `(ref func)`, `toCore` writes
  `funcref`); `Lime1.Module.toCore_eq_retype`: the two images differ only there;
* `Lime1.Validation.ModuleValid.toCoreBinary`, `Lime1.Execution.Instantiation.toCoreBinary`,
  `InstantiationDiverges.toCoreBinary`: validity and instantiation carry over to
  `toCoreBinary`.

The model-level statements are in `Silmaril.Wasm.Models.Lime1Bin`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.Binary.lime1_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Binary.lime1_core

/-- info: 'Silmaril.Wasm.Binary.v1_lime1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Binary.v1_lime1

/-- info: 'Silmaril.Wasm.Lime1.Execution.Instantiation.toCoreBinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Lime1.Execution.Instantiation.toCoreBinary

/-- info: 'Silmaril.Wasm.Lime1.Validation.ModuleValid.toCoreBinary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.Lime1.Validation.ModuleValid.toCoreBinary
