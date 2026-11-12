module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.BackwardLane
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Encoding
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadLane
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StepLift
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.Restrict
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadLaneBwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadPack
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.LoadPackBwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.DispatchD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.ReadMS
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StateF
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.TransferD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StoreD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.AssembleD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.TypedD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.EntryD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.AssembleRest

/-!
# SpecTec ↔ Core 3.0, round 7: memory SIMD stores, forward (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd`; see `docs/projects/spectec/README.md`

With the memory SIMD store encoded by `Round6.MemSimd.instrToVM` (against the IL type `instr`)
instead of the provisional `schemaInstrV`, each of Core's four vector store steps is matched by
the corresponding SpecTec `Step` rule, from a typed state image. The rule fires (`Fires … k`), so
the step holds in both the declarative reading `SStep` and round 6's backend reading
`Round6.Int.backend` (`both_of_fires`, through `Round6.Reading.firesB_step_iff`):

| Core (`MemoryStep`) | SpecTec rule | theorem |
| --- | --- | --- |
| `vecStoreOob` | 22 `vstore-oob` | `fwd_vecStoreOob` (every `B`) |
| `vecStoreVal` | 23 `vstore-val` | `fwd_vecStoreVal` (given `VBytes`; `vBytes_withVBytes`) |
| `vecStoreLaneOob` | 24 `vstore_lane-oob` | `fwd_vecStoreLaneOob` (every `B`) |
| `vecStoreLaneVal` | 25 `vstore_lane-val` | `fwd_vecStoreLaneVal` (at `withVBytes (Prims.builtins …)`, in-range lane) |

`fwd_vecStore_builtins` packages 22 and 23 at `withVBytes (Prims.builtins P hn host)`.

Backward, for all four rules. Rule 25 (`bwd_vstoreLaneVal`, `bwdB_vstoreLaneVal`, at
`withVBytes (Prims.builtins …)`) recovers the lane shape from its premises: `$lanes_` is defined
only at the image of a shape (`lanes_inv`), the selected lane is a `%`-numeral only at an integer
shape (`laneV_pct`), and `N = $jsize(Jnn)` then fixes the pack size (`packOf_of_jsize`).
For rules 22, 23 and 24: `bwd_vstoreOob`, `bwd_vstoreVal`, `bwd_vstoreLaneOob` (declarative
`Fires`, for a `B` that does not interpret `$mem`/`$with_mem`) and `bwdB_vstoreOob`,
`bwdB_vstoreVal`, `bwdB_vstoreLaneOob` (backend `FiresB`, at `withVBytes (Prims.builtins …)`).
If the rule fires at the image of a vector store, the result is the image of Core's successor
(trap, or the stored state), and Core's `vecStoreOob`/`vecStoreVal`/`vecStoreLaneOob` steps there.
`vstore-val` needs the frame to resolve the memory, which validation gives.
`$vbytes_` is not answered by round 6's `Prims.builtins`, so rule 23 never fires in
`simEnv (BI …)`; `withVBytes` adds it.

**Loads (`Step_read`), out of bounds.** The five trap rules (42 `vload-num-oob`, 44
`vload-pack-oob`, 46 `vload-splat-oob`, 48 `vload-zero-oob`, 50 `vload_lane-oob`) are simulated
in both directions at the `instrToVM` encoding: `fwd_vecLoadOob`, `fwd_vecLoadLaneOob` (a
`Step_read` step in both `SRead` and round 6's `SReadB`, from a typed state image) and
`bwd_vloadOob`, `bwd_vloadLaneOob`, `bwdB_vloadOob`, `bwdB_vloadLaneOob` (the rule at the load's
shape, `oobRule op`, fires only with result `TRAP`, and Core's `vecLoadOob`/`vecLoadLaneOob`
steps).

**Loads, in bounds.** `fwd_vecLoadFull`: `v128.load` (rule 43 `vload-num-val`) forward, at
`withVBytes B`.

Pass 4 adds:

* **rule 43 backward**: `bwd_vloadNumVal`, `bwd_vloadFull`, `bwdB_vloadFull`. The quantified
  `c : vec_(V128)` is a numeral below `2 ^ 128` (`vec_inv`, through `vN` and `uN(128)`; `uN_inv_lt`
  inverts `uN(N)` at every width), so `$vbytes_` determines it (`Read2.leBytesV_inj`) and it is
  Core's loaded vector;
* **rule 49 (`vload-zero-val`) both ways**: `fires_vloadZeroVal`, `fwd_vecLoadZero` (given
  `BytesFuns` and `FloatB`, both proved at `withVBytes (Prims.builtins …)`: `bytesFuns_vb`,
  `floatB_vb`), `bwd_vloadZeroVal`, `bwdB_vecLoadZero` (`j : iN(N)` is below `2 ^ N`,
  `iN_inv_lt`; `$extend__(N, 128, U, j)` is the zero extension, `applies_extend128`);
* **rule 47 (`vload-splat-val`) both ways**: `fires_vloadSplatVal`, `fwd_vecLoadSplat_shape`
  (`lanesV_splat`: the lanes of Core's splat are the word, once per lane), and backward
  `bwd_vloadSplatVal`, `bwdB_vecLoadSplat` (`$inv_lanes_` answers only at a shape image,
  `invLanes_inv`; a `%`-numeral lane forces an integer shape; `N = $jsize(Jnn)` fixes the pack
  size);
* **rule 51 (`vload_lane-val`) both ways**: `fires_vloadLaneVal`, `fwd_vecLoadLane_shape`, for an
  in-range lane (`lanesV_setLane`), and backward `bwd_vloadLaneVal`, `bwdB_vecLoadLane` (the
  list update succeeds only in range, `updLanes_inv`, `lanePrem_inv`);
* **the loads as `Step` steps** (`StepLift.lean`): `step_of_read` lifts a `Step_read` step through
  `Step/read` in both readings, and `stepFwd_vecLoadOob`, `stepFwd_vecLoadLaneOob`,
  `stepFwd_vecLoadFull`, `stepFwd_vecLoadZero`, `stepFwd_vecLoadSplat`, `stepFwd_vecLoadLane` are
  Core's vector loads as single-redex SpecTec `Step` steps;
* **the target on its memory-SIMD-free part** (`Restrict.lean`):
  `wholeStepValidRMNoMS_backend : WholeStepValidRMNoMS`, from round 6, through
  `boundedSel_of_boundedSelM` and `noMemSimd_of_configEq`.

**The configuration-level encoding and the extended domain** (`Defs.lean`): `configVD` re-encodes
memory SIMD at every depth and is `configV` off memory SIMD code (`configVD_eq_of_noMemSimd`,
`configVD_eq_of_bounded`); `BoundedSelM` admits memory SIMD and contains round 6's `BoundedSel`
(`boundedSelM_of_boundedSel`). With them `Round7.Task.wholeStepValidRM` is **stated** (frozen).

* **rule 45 (`vload-pack-val`) forward** (`LoadPack.lean`): `fires_vloadPackVal`,
  `fwd_vecLoadPack`, `stepFwd_vecLoadPack`. The iterated byte premise is built round by round
  (`dprem_iterListN1`), lane `l`'s bytes are the sub-slice at `l * K/8` (`leBytesV_lane`,
  `drop_take_encL`), and the result iteration is evaluated by `evalExp_iterListN1`.

* **rule 45 backward** (pass 5, `LoadPackBwd.lean`): `bwd_vloadPackVal`, `bwd_vecLoadPack`,
  `bwdB_vecLoadPack`. The iterated byte premise is inverted row by row
  (`premW_iterListN1_inv`, `packRow_inv`), the rows assemble into Core's 8-byte load
  (`load_of_packRows`), `$jsizenn(Jnn) = K * 2` fixes the `$extend__` width, and `$inv_lanes_`
  is read back at an integer shape (`invLanes_inv`, `laneV_pct`, `lanesV_extendLanes`). Every
  memory SIMD rule (`Step` 22–25, `Step_read` 42–51) is now simulated in both directions.

* **round 6's generic backward dispatch at `configVD`** (pass 5, `DispatchD.lean`,
  `ReadMS.lean`): `backward_upToD` re-runs `Round6.Target.backward_upToVC` at `configVD`, from
  `TypingFactsD` and the per-rule obligations `BackwardUpToD` (`Defs.lean`); the decoders and
  typing facts it needs are proved (`structDecodeD_simEnv`, through `adminToVD_case`, and
  `typingFactsD_simEnv`). The ten memory SIMD
  `Step_read` obligations were discharged for stores without memory SIMD code (the
  left-hand sides decode to `v128.load…` / `v128.loadN_lane` images, `decode_vloadD`,
  `decode_vloadLaneD`; `vload_kind_*` match the rule to the load shape), and the dispatch
  with them plugged in, from `BackwardUpToDRest`; pass 6 drops the store hypothesis
  (`readMSD`, `backward_upToD_restD`).

**Not done:** the proof of `Round7.Task.wholeStepValidRM`: round 6's whole chain is about `configV` and `BoundedSel`, and
each of its lemmas that mentions them would have to be re-run at `configVD` and `BoundedSelM`
(or transported by a theorem not available here).

Pass 6 adds:

* **the memory SIMD loads at stores holding memory SIMD code**: the backward load leaves are
  stated at `stateVF F s f` (`StateF.lean`: the store encoding with any `FUNCS` value, of which
  `stateV` and `stateVD` are instances), so `readMSD` and `backward_upToD_restD` drop pass 5's
  `StoreMS` hypothesis (pass 5's conditional forms `readMS`, `backwardUpToD_of_rest`,
  `backward_upToD_rest` are removed);
* **the memory SIMD stores at `configVD`** (`StoreD.lean`): `stepMSD` discharges the `Step`
  obligations 22–25 at every configuration. Rules 23 and 25 recover the memory from the firing
  rule (`withMem_resolvesF`) and keep the store's functions (`bwd_vstoreValF`,
  `bwd_vstoreLaneValF`); `backward_upToD_restS` is the backward recursion with every memory SIMD
  rule plugged in, from the obligations `BackwardUpToDRestS` of the rules without memory SIMD;
* **the backend transfer at `configVD`** (`TransferD.lean`): `sstepB_iff_of_not_castRedexD`,
  `transferD_backend`: away from cast redexes, `Round6.Int.backend` and `SStep` have the same
  successors at the `configVD` image of every configuration, for every `B` and encoding
  (round 6's `Transfer.sstepB_iff_of_not_castRedex` at `configVD`);
* **the target from its open leaves** (`AssembleD.lean`): `wholeStepValidRM_of_open` proves
  `Round7.Task.wholeStepValidRM` from `OpenRM` (the declarative forward half, the entry predicate
  and typing at `configVD`, the per-rule obligations `BackwardUpToDRestS` and the cast leaf).
  It is a reduction; `OpenRM` is not proved.

Pass 7 proves three fields of `OpenRM`, at `V := NoCastVM`:

* **`typed`** (`TypedD.lean`): `typedD_of_configOk_selM`, round 5's positive typing
  (`Round5.Target.typed_of_configOk_sel`) re-run at `configVD` on `BoundedSelM`; memory SIMD
  instructions are typed by round 6's `typedV_vecMemV`, block bodies are re-encoded by
  `instrsToVD`;
* **`closed`, `entry`** (`EntryD.lean`): `ReadValidSM` and `NoCastVM`, the `M` analogues of
  round 5's `ReadValidS` and round 6's `NoCastV`, with `noCastVM_closed` and `noCastVM_entry`;
* `wholeStepValidRM_of_rest` (`AssembleRest.lean`) reduces the target to `OpenRMRest`, the
  fields still open: `forward`, `rest` (at `NoCastVM`), `castsFwd`, `castsBwd`.
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

open Silmaril.Wasm.SpecTec.Sim

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecStoreOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecStoreOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecStoreVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecStoreVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecStoreLaneOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecStoreLaneOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecStoreLaneVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecStoreLaneVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecStore_builtins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecStore_builtins

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vstoreOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vstoreOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vstoreLaneOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vstoreLaneOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vstoreVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vstoreVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwd_vstoreLaneVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwd_vstoreLaneVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vstoreLaneVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vstoreLaneVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadLaneOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadLaneOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vloadOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vloadOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vloadLaneOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vloadLaneOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadFull

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.configVD_eq_of_noMemSimd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.configVD_eq_of_noMemSimd

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.configVD_eq_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.configVD_eq_of_bounded

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.boundedSelM_of_boundedSel' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.boundedSelM_of_boundedSel

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.vec_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.vec_inv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vloadFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vloadFull

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadZero

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vecLoadZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vecLoadZero

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadSplat_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadSplat_shape

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadLane_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadLane_shape

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.stepFwd_vecLoadLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.stepFwd_vecLoadLane

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.wholeStepValidRMNoMS_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.wholeStepValidRMNoMS_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vecLoadSplat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vecLoadSplat

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vecLoadLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vecLoadLane

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.fwd_vecLoadPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.fwd_vecLoadPack

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwd_vloadPackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwd_vloadPackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwdB_vecLoadPack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwdB_vecLoadPack

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.backward_upToD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.backward_upToD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.structDecodeD_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.structDecodeD_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.typingFactsD_simEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.typingFactsD_simEnv

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.readMSD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.readMSD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.backward_upToD_restD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.backward_upToD_restD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.sstepB_iff_of_not_castRedexD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.sstepB_iff_of_not_castRedexD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.transferD_backend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.transferD_backend

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.wholeStepValidRM_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.wholeStepValidRM_of_open

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.stepMSD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.stepMSD

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.backward_upToD_restS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.backward_upToD_restS

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.bwd_vstoreLaneValF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.bwd_vstoreLaneValF

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.typedD_of_configOk_selM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.typedD_of_configOk_selM

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.noCastVM_closed' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.noCastVM_closed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.noCastVM_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.noCastVM_entry

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.wholeStepValidRM_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round7.MemSimd.wholeStepValidRM_of_rest
