module

public import Silmaril.Wasm.SpecTec.Sim20.VecNum.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumLk
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumUndef
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumCheck
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumLanes

/-!
# The vector numeric dispatchers of wasm-2.0 as builtins: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecNum`; see `docs/projects/spectec/README.md`, "fwd20".

* `VecNumUndef`: a syntactic check `clauseUnb` (first premise an `if` test iterating over a
  variable that the pure argument patterns do not bind) and **`tryClausesUndef_of_all`**: a clause
  list that passes it definitely fails at every argument list, in every environment.
* `VecNumLk`, `VecNumCheck`: `$vunop_`, `$vbinop_`, `$vrelop_` in `simEnv20V B` are
  `Original.d263`–`d265`, and every clause passes the check (`clauseUnb_vunop`, … ,
  `decide +kernel`).
* `VecNumB`: **`applies_vunop`** (and `_vbinop`, `_vrelop`): the dispatchers denote exactly what the
  builtins answer. **`not_vecNumAgree`**: round 7's `VecLane.VecNumAgree` fails wherever `$vunop_`
  is unanswered, in particular at round 7's builtins (**`not_vecNumAgree_vecB`**).
  **`vecNumAgree_vecNB`**: it holds at `vecNB P`, all six fields.
* `VecNumStep`: the float `vunop`/`vbinop`/`vrelop` lifts at `vecNB P` without the numerics
  hypothesis (`sstepV_vecFloatUnOp_vecNB`, …).
* `VecNumLanes`: **`vecFloatUnOpResult_lanes`**: the float `vunop` answers of `vecNB P` are the
  set product of the lane-wise scalar results put back with `$inv_lanes_`, i.e. the clause read
  with binding `if` premises, at both NaN policies.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.tryClausesUndef_of_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.tryClausesUndef_of_all

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.applies_vunop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.applies_vunop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.not_vecNumAgree_vecB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.not_vecNumAgree_vecB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.vecNumAgree_vecNB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.vecNumAgree_vecNB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.sstepV_vecFloatBinOp_vecNB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.sstepV_vecFloatBinOp_vecNB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecNum.vecFloatUnOpResult_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecNum.vecFloatUnOpResult_lanes
