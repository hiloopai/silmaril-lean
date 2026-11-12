module

public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.R4Fwd.Concrete

/-!
# SpecTec ↔ Core 3.0, round 4, track r4-fwd: what is proved

Core → SpecTec (`docs/projects/spectec/README.md`):

* `R4Fwd.forward_all`: the forward recursion over Core's `Step` on **every** configuration with a
  bounded store (no fragment), up to call annotations, from round 2/3's bundles, `ZBytes.ZB`,
  `ExpandInv` and the obligations `Open4` (non-bitwise SIMD, memory SIMD, `array.new_data-num`,
  `array.init_data-zero`);
* `R4Fwd.forward_concrete4`, `forward_concrete4_valid`: the forward conjunct `Forward … V` for the
  concrete `Prims.builtins`, for every validity predicate `V`;
* `R4Fwd.fwd_aggregate_any`: every other aggregate step at every frame, **packed fields
  included** (`$packfield_`, `$unpackfield_`, `$unpack`, `$sx` evaluated at packed types),
  `array.new_elem-alloc`, `array.new_data-oob`, `array.init_data-oob2` and `array.init_data-num`
  (`$zsize`, `$zbytes_`, `$cunpack`, `$cunpacknum_`, `$const` evaluated; `lit_` typed,
  `litTyping_simEnv`);
* `R4Fwd.zB_builtins`, `R4Fwd.expandInv_builtins`: both side conditions hold for
  `Prims.builtins`;
* `R4Fwd.open4Vector_of_agree`: `Open4.vector` from family V's `VecTyping` and `VecAgree`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.forward_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.forward_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.forward_concrete4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.forward_concrete4

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.fwd_aggregate_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.fwd_aggregate_any

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.open4Vector_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.open4Vector_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.fwd_arrayInitDataNum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.fwd_arrayInitDataNum

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.litTyping_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.litTyping_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.R4Fwd.expandInv_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R4Fwd.expandInv_builtins
