module

public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.FwdSimdAgg.Assembly

/-!
# SpecTec ↔ Core 3.0, round 3 track `fwd-simd-agg`: what is proved

Forward (Core → SpecTec) lemmas at `simEnv B`, wired into `Integrate.forward_wide`:

* the bitwise vector instructions `v128.not`, `v128.and`, `v128.andnot`, `v128.or`, `v128.xor`,
  `v128.bitselect`, `v128.any_true` (`fwd_vecUnOp`, `fwd_vecBinOp`, `fwd_vecTernOp`,
  `fwd_vecTestOp`), with `$vvunop_`, `$vvbinop_`, `$vvternop_`, `$vsize`, `$inez_` evaluated
  and the operator typing proved, under `IntB B` and `VVB B`;
* `struct.new_default`, `array.new_default` (`fwd_structNewDefault`, `fwd_arrayNewDefault`), with
  `$default_($unpack(zt))` evaluated at every closed unpacked storage type;
* `array.copy-le`, `array.copy-gt`, `array.init_elem-succ` (`fwd_arrayCopyLe`, `fwd_arrayCopyGt`,
  `fwd_arrayInitElemSucc`), so every `array.copy` and `array.init_elem` constructor is covered;
* `vvB_builtins`: the concrete `Prims.builtins` satisfies `VVB`.

Finding: `$sx` has no clause at a reference type (`FwdSimdAgg/Defs.lean`), so without `B`'s
fallback `array.copy` on an array of references is stuck in SpecTec.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.fwd_vector_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdSimdAgg.fwd_vector_wide

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.fwd_aggregate_wide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdSimdAgg.fwd_aggregate_wide

/-- info: 'Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.vvB_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FwdSimdAgg.vvB_builtins
