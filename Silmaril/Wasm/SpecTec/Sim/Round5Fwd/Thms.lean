module

public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5Fwd.InitZero

/-!
# SpecTec ↔ Core 3.0, round 5, track fwd: what is proved

Core → SpecTec (`docs/projects/spectec/README.md`), for `B := Prims.builtins P hn host`:

* `Round5.Fwd.forward5`: the forward recursion over Core's `Step` from every bounded
  configuration, up to call annotations, with **no** refuted bundle (`Integrate.Residue`,
  `Integrate.Extra`, `Whole.Assumptions`) and without round 4's `Open4.vecMem`: every family
  structure is the one proved for the concrete `B`; the rules whose earlier proofs used a refuted
  field are the obligations `Round5.Fwd.Obl`;
* `Round5.Fwd.forward_valid5`: the `fwd` field of `Round4Int.Parts` from `Obl`;
* `Round5.Fwd.parts_of_obl`: `Round4Int.Parts` with that field from `Obl`;
* `Round5.Fwd.not_vecMem`: bounded code holds no memory SIMD instruction;
* `Round5.Fwd.tyBnd_of_expand`: the expansion of a bounded defined type is bounded (with
  `tyBnd_subst`, `tyBnd_unrollrt`);
* `Round5.Fwd.obl_of`, `forward_valid_of`: eleven of `Obl`'s fields (`block`, `loop`,
  `try_table`, the `call_ref` rules, `return_call_ref`-frame-addr, `throw`, the `throw_ref`
  handler rules) from `TypesB` (bounded positive type typing, open) and, for the host calls,
  `HostFinite` and `Prims.HostRespects`; the rest (`Rest`: non-bitwise SIMD, aggregates, casts)
  stays open;
* `Round5.Fwd.rest_of`, `forward_valid_tb`: the four cast rules from `RefOkB` (the `Ref_ok`
  bridge on typed stores and bounded reference types, open), with `tyBnd_instRef`; so the
  forward conjunct holds from `TypesB`, `RefOkB`, the host conditions, the non-bitwise SIMD
  operators and the aggregate steps;
* `Round5.Fwd.fwd_aggregate5`, `forward_valid_agg`: every aggregate step from `AggTypesB`
  (`Aggregates.AggTypes` on bounded types, from `TypesB`: `aggTypesB_of`), with
  `array.new_data-num`/`array.init_data-zero` as the bounded obligations `NewDataNumB`,
  `InitDataZeroB`;
* `Round5.Fwd.fwd_arrayInitDataZero5`, `initDataZeroB_builtins`: `array.init_data-zero` forward
  (round 4's `Open4.initDataZero`), in every `simEnv B`: at `n = 0` the `-oob2` bound does not
  depend on the element type (`bound_zero_inv`);
* `Round5.Fwd.forward_valid_final`: the forward conjunct from `TypesB`, `RefOkB`, the host
  conditions, the non-bitwise SIMD operators and `NewDataNumB`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward_valid5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward_valid5

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.parts_of_obl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.parts_of_obl

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.obl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.obl_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward_valid_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward_valid_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.tyBnd_of_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.tyBnd_of_expand

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward_valid_tb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward_valid_tb

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward_valid_agg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward_valid_agg

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.initDataZeroB_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.initDataZeroB_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Fwd.forward_valid_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Fwd.forward_valid_final
