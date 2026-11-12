module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Assemble
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.Numeric

/-!
# SpecTec ↔ Core 3.0, round 5, track pos: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Pos`; see `docs/projects/spectec/README.md`.

**Refutations.**

* `not_succTyped`, `not_parts_all`: `Round4Int.Parts.succTyped` fails for a finite host that
  returns a store holding an invalid function body (`SuccTyped.lean`).
* `tryClauses_utf8`: `$utf8` of a one-element list is `outOfFuel` at every fuel, in every
  `simEnv B` (its first clause matches its own recursive call), so no primitive can answer it;
  `not_hasTyp_name_single`, `not_typedV_moduleinst_of_export` (`Utf8.lean`).
* `not_posTyping`, `not_parts`: `Round4.PosTyping` and `Round4Int.Parts` are uninhabited;
  `not_typed_expNopCfg`: a valid, bounded configuration that is not `Typed` (`Refute.lean`).
* `stepRules_guarded`, `not_sstep_of_frame`: no SpecTec `Step` fires from an ill-typed frame
  (`Guard.lean`).
* `not_wholeStepValid`: **`Round4.Task.wholeStepValid` is false**; `not_wholeStepValid_hostOk`:
  so is its restriction to `HostOk` hosts.

**The restated target** `Round5.Task.wholeStepValidOk` (header `Defs.lean`: `HostOk` hosts,
export-free configurations) and its reduction `wholeStepValidOk_of_parts` from `PartsOk`
(`PosTypingNE`, the forward conjunct, `FamBwdV`, `RemainingV`), with
`typed_of_configOk_ne`.

**Positive typing (fields of `PosTypingNE`), in every `simEnv B`.**

* `tyT_tyV`, `typedV_deftype`: every bounded runtime type is typed at its sort (`Types.lean`);
* `typedV_callRefType`, `typedV_returnCallRefType`: the `callRefType` and `returnCallRefType`
  fields, without validity;
* `typedV_moduleinst_ne`, `moduleinst_ne`: the `moduleinst` field (`Module.lean`);
* `typedV_store_ne`: the `store` field, from `InstrTyping` for the function bodies (`Insts.lean`
  types every other instance from its bounds; `Store.lean`);
* `posTypingNE_of_instr : InstrTyping B → PosTypingNE B hn`, `partsOk_of_instr`: the positive
  typing reduces to its `instr` field.

* `typedV_instrToV_of`, `instrTyping_of_open : OpenTyping B → InstrTyping B`,
  `posTypingNE_of_open`: every instruction outside `InstrOpen` is typed (blocks through their
  bodies), so the positive typing reduces to the open classes (`Instr.lean`).

* `openTyping_of_simd : SimdTyping B → OpenTyping B`, `posTypingNE_of_simd`: the scalar numeric
  operators, conversions, loads and stores are typed too (`Numeric.lean`).

Open: `SimdTyping` (the SIMD instructions other than `v128.const`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_succTyped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_succTyped

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_parts_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_parts_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.tryClauses_utf8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.tryClauses_utf8

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_hasTyp_name_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_hasTyp_name_single

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_posTyping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_posTyping

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_parts

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_typed_expNopCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_typed_expNopCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_sstep_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_sstep_of_frame

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_wholeStepValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_wholeStepValid

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.not_wholeStepValid_hostOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.not_wholeStepValid_hostOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.typed_of_configOk_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.typed_of_configOk_ne

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.wholeStepValidOk_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.wholeStepValidOk_of_parts

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.tyT_tyV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.tyT_tyV

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.typedV_callRefType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.typedV_callRefType

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.typedV_returnCallRefType' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.typedV_returnCallRefType

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.moduleinst_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.moduleinst_ne

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.typedV_store_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.typedV_store_ne

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.posTypingNE_of_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.posTypingNE_of_instr

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.partsOk_of_instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.partsOk_of_instr

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.typedV_instrToV_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.typedV_instrToV_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.instrTyping_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.instrTyping_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.posTypingNE_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.posTypingNE_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.openTyping_of_simd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.openTyping_of_simd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Pos.posTypingNE_of_simd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Pos.posTypingNE_of_simd
