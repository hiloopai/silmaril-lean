module

public import Silmaril.Wasm.SpecTec.Sim20.VecTyp.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypCheck
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTyp20
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypFam
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypInt
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypStep
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTypLanes

/-!
# State typing does not depend on the vector builtins: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecTyp`; see `docs/projects/spectec/README.md`, "vec".

* `bagreeAt`, `tbagreeAt` (unrefined, `Raw/…/Sim20/VecTyp/{Eval,Typ}.lean`): copies of
  `RelFree.agreeAt`/`tAgreeAt` for two builtins that agree away from `bad` (`BAgree`).
  **`typedV_withB`** (`VecTypEq`): typing at a harmless type moves between them.
* `defsTypsOkB_fixedT20` (`VecTypCheck`, kernel): in `fixedT20` no type, and no definition
  outside `badV20`, refers to a relation or to `badV20`.
* **`state_vecNB_of_good20B`**, `code_vecNB_of_good20B` (`VecTyp20`): a `Good20B` configuration
  at `storeB P` is typed at `simEnv20T (vecNB P)` (`bAgree_vecNB`, `typedV_vecNB`).
* `hasTyp_famOf_typedA` (`VecTypFam`): a typed `VUNOP`/`VBINOP`/`VRELOP` instruction of
  `simEnv20V B` types its operator at the family.
* `fwd_vecIntUnOp20V`, … (`VecTypInt`) and **`sstepV_vecIntUnOp`**, … (`VecTypStep`): the integer
  vector operators as `Step`s, under `VecNumAgree`, given the instruction typed.
* **`sstepV_vecFloatUnOp_good20B`** … **`sstepV_vecIntRelOp_good20B`** (`VecTypStep`): all six
  vector operator lifts at `vecNB P` from a `Good20B` configuration, with no typing or numerics
  hypothesis left (integer operators: the instruction occurs in the configuration's code).
* `vecFloatBinOpResult_lanes`, `vecFloatRelOp_lanes`, `vecIntUnOpResult_lanes`,
  `vecIntBinOpResult_lanes`, `vecIntRelOp_lanes` (`VecTypLanes`): the answers of `vecNB P` lane by
  lane.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.typedV_withB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.typedV_withB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.state_vecNB_of_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.state_vecNB_of_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.hasTyp_famOf_typedA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.hasTyp_famOf_typedA

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.sstepV_vecIntBinOp_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.sstepV_vecIntBinOp_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.sstepV_vecFloatUnOp_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.sstepV_vecFloatUnOp_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecTyp.vecFloatBinOpResult_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecTyp.vecFloatBinOpResult_lanes
