module

public import Silmaril.Wasm.SpecTec.Sim10.Num.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.NumAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.PureNumBwd

/-!
# The 1.0 numeric agreement: what is proved

* `Sim10.Whole.numAgree10_simEnv10 : IntB B → FloatB P B → NumAgree10 (simEnv10 B) P`: the
  wasm-1.0 script's `$unop_`, `$binop_`, `$testop_`, `$relop_` and `$cvtop__` return V1's numeric
  results, under the builtins the 2.0 and 3.0 numerics take. The integer library wasm-1.0 shares
  with 2.0 and 3.0 is 16 of `Equiv.NumEnvCore`'s 24 definitions (`Sim10.NumEnv10`, by kernel
  `rfl`); its bit operations are builtins, answered by `IntB`.
* `Sim10.Whole.numAgree10_floatIntB : NumAgree10 (simEnv10 (floatIntB P)) P`, at every profile.
* `Sim10.Whole.bwd10_num`: under `NumAgree10` at the spec profile, every firing of `Step_pure`
  20–27 at the image of V1 code is the image of a V1 `PureStep`. `unop-trap`, and `binop-trap` at
  a float type, never fire.
-/

@[expose] public section

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.numAgree10_floatIntB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.numAgree10_floatIntB

/--
info: 'Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_num' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.SpecTec.Sim10.Whole.bwd10_num
