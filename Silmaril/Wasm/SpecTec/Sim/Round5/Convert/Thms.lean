module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Convert.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Convert.Open5

/-!
# SpecTec ↔ Core 3.0, round 5, track convert: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim.Round5.Convert`; see `docs/projects/spectec/README.md`.

* `tryClausesUndef_vcvtop`: every clause of `$vcvtop__` definitely fails where its three leading
  conditions evaluate (`CondsOk`); `evals_cond₁_extend`, `evals_cond₁_convert`,
  `evals_cond₁_trunc`, `evals_cond₂`, `evals_cond₃`, `condsOk_builtins`: they do, at the concrete
  builtins, for every operator and all shape values.
* `undef_vcvtop`, `vecConvertR_builtins`: the clauses definitely fail at every shape pair, operator
  and operand, so `Simd.VecConvertR` holds at the concrete builtins (track simd's
  `vecConvertR_of_undef`).
* `vecAgreeNC_of_lanes`, `vecAgreeNC_builtins`: family V's `VecAgree` without `convert`, at the
  concrete builtins; `fwdN_vec…` (copied from family V), `fwdN_vecConvertR`, `fwd_convertR`,
  `fwd_vectorR`: the forward vector steps, matched exactly except `vcvtop`, which goes to the result
  `$vcvtop__` picks.
* `vectorFwdR_of`, `vectorFwdR_builtins`, `vectorFwdDet_of_R`, `vectorFwdDet_builtins`: the
  restated forward vector obligation, unconditionally; `Round5.Int.VectorFwd` on the steps Core
  takes deterministically.
* `open5_of_open4`, `open5_iff`, `vectorFwdR_of_open5`, `not_open5`: `Open5` is `simd ∧ refOk`,
  and unsatisfiable through `simd`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Convert.vecConvertR_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Convert.vecConvertR_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Convert.vectorFwdR_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Convert.vectorFwdR_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Convert.vectorFwdDet_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Convert.vectorFwdDet_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Convert.open5_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Convert.open5_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round5.Convert.not_open5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Round5.Convert.not_open5
