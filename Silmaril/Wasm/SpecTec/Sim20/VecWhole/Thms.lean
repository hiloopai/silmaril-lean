module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.VecWhole.Core
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeCtx
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeFlat
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeValid
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeEntry
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholePrims

/-!
# Vector code forward at `simEnv20V (vecNB P)`: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.VecWhole`; see `docs/projects/spectec/README.md`, "vec".

* `VecWholeCtx`: `Step`'s rules 2–4 are unchanged in the corrected vector script, so
  **`sstepV_ctxtInstrs`**, `sstepV_ctxtLabel`, `sstepV_ctxtFrame` lift steps of `simEnv20V B`
  through the three evaluation contexts; the `LABEL_`/`FRAME_`/`state` typing inversions at
  `simEnv20V B`.
* `VecWholeBase`: the invariant `TypV B hn` (state and code typed in `simEnv20V B`), the covered
  redexes `VecSrc` (the six operator families at both lane kinds, `extract_lane` at every shape),
  and **`fwd_vecBase`**: each covered V2 step is a `Step` of `simEnv20V (vecNB P)` from a `TypV`
  configuration, with a `TypV` successor.
* `VecWholeNest`: **`fwd_nestV`** (any base fragment at `simEnv20V B`, closed under the three
  contexts at any depth) and **`fwd_vecNest`**, `runV_vecNest`.
* `VecWholeFlat`: straight-line vector code `vecOkA`; **`cover_vec`** (every V2 step from it is a
  nested covered step), **`wholeStepVec`**, **`wholeRunVec`**.
* `VecWholeValid` (with the evaluation slices `VecWholeIU*`, `VecWholeIB*`, `VecWholeIR*`):
  **`typedA_vecIntUnOp_valid`**, `typedA_vecIntBinOp_valid`, `typedA_vecIntRelOp_valid`: every
  integer vector operator V2 validates is a typed `admininstr` of `simEnv20V B`.
* `VecWholeEntry`: **`typV_of_good20B`**, **`wholeRunVec_good20B`**; an earlier integer
  `_good20B` lifts are vacuous (**`not_mem_vecIntUnOp_good20B`**, …) and are restated from
  validity (`sstepV_vecIntUnOp_valid`, …).
* `VecWholeEnv`, `VecWholePrims`, `VecWholeNC`, `VecWholeUn` and the unrefined copy
  `Raw/…/Sim20/VecWhole/Core`: the script's lane primitives with clauses compute V2's lane
  functions (`callDef_iaddSat_lane`, …); `$ipopcnt_` does at `IntB` builtins; `$iavgr_`,
  `$iq15mulr_sat_`, `$fpmin_`, `$fpmax_` denote nothing at `vecNB P`
  (**`not_callDef_unanswered`**).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_ctxtInstrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_ctxtInstrs

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_ctxtFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_ctxtFrame

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_vecBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_vecBase

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_nestV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_nestV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_vecNest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.fwd_vecNest

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.cover_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.cover_vec

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeStepVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeStepVec

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeRunVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeRunVec

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.typedA_vecIntBinOp_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.typedA_vecIntBinOp_valid

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.typedA_vecIntRelOp_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.typedA_vecIntRelOp_valid

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.typV_of_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.typV_of_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeRunVec_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.wholeRunVec_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.not_mem_vecIntUnOp_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.not_mem_vecIntUnOp_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_vecIntBinOp_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.sstepV_vecIntBinOp_valid

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.numEnvCore_simEnv20V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.numEnvCore_simEnv20V

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.callDef_iaddSat_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.callDef_iaddSat_lane

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.callDef_ipopcnt_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.callDef_ipopcnt_lane

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.VecWhole.not_callDef_unanswered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.VecWhole.not_callDef_unanswered
