module

public import Silmaril.Wasm.SpecTec.Sim20.Whole.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTags
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeStuck
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeDead
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeDecode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveCtrl
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveNum
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeLiveRef
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCvtEdge
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwdQ
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeVecEdge
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeVecRefute
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeBwdW
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeResEdge
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestInert
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestDrop
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestTable
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeConstBound
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestSize
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestFill
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestMemFill
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestCopy
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestInit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestMemInit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestCopyGt
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestStoreTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeRestGrow
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowAnswer
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowB
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrow10
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGrowFwd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdGrow
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdTop
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeValTyping
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVar
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStore
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCtxS
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeCtxAgree
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdS
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeSubjRed
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPR
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeStoreVac
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStoreVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPure2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStoreLane
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdStoreFrag
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCover
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholePlainTail
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCoverP
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdBlock
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCallAddr
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdLoad
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCallInd
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdCallIndTrap
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGoodCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeGoodRun

/-!
# The 2.0 whole-step targets: what is proved

Namespace `Silmaril.Wasm.SpecTec.Sim20.Whole`; see `docs/projects/spectec/README.md`.

* `closed_step20`, `sstepB20_iff`, `sreadB20_iff` (`WholeTags`): `Step`, `Step_pure` and
  `Step_read` of the wasm-2.0 script are closed, so the Round 6 backend reading of `Step` is the
  declarative reading.
* `pureTags20_eq`, `readTags20_eq`, `stepTags20_eq` (kernel `rfl`) and `not_dderives_of_table`.
* `stuck_nopNop` (`WholeStuck`): `z; NOP NOP` has no step in the wasm-2.0 script, at every `z`
  and every primitives `B`; `step_nopNop`: V2 reduces it (`Step.ctxtInstrs`).
* `not_wholeStepValid : ¬ Task.wholeStepValid`: the forward half fails, at a configuration
  whose image is typed (`typed20_nopNop`).
* `backward20_of_parts`, `wholeStepBwd_of_parts` (`WholeBwd`): the backward half from the
  per-rule obligations `BwdParts20`, with the four structural rules of `Step` (`pure`, `read`,
  `ctxt-label`, `ctxt-frame`) handled for every configuration (`inv_*20`, `bwd_*20`).
* `stuck_unreachable`, `not_fwd_unreachable` (`WholeTyping`): `Step/pure` and `Step/read`
  quantify their code as `instr*`, and `TRAP` is not an `instr` (`admin_not_instr`), so
  `z; UNREACHABLE` is stuck as well: the forward half fails on one instruction, independently of
  the missing `ctxt-instrs`.
* `not_firesPure_dead`, `not_firesRead_dead`, `bwdParts20_of_live`, `wholeStepBwd_of_live`
  (`WholeDead`): 15 `Step_pure` and 21 `Step_read` rules force a non-`instr` constructor on one
  side (`deadPure20_ok`, `deadRead20_ok`, kernel `rfl`), so `Step` never uses them: no block or
  loop is entered, no function is called, nothing traps through `Step/pure` or `Step/read`. The
  backward obligations reduce to the live rules (`BwdLive20`).

Pass 6:

* `WholeDecode`: `adminHead20`, `adminToV_case20`, the `head20_*` inversions, `admin_of_valHead`,
  `fires_list20`, `codes20_*`, `val20_of_var`: V2 code is read back from its image.
* `WholeLiveCtrl`, `WholeLiveNum`, `WholeLiveRef`: the 18 live control, numeric, reference and
  `local.tee` rules of `Step_pure` backwards at **any** V2 code (`bwdPure_*`; the numeric ones
  under `IntB B` and `FloatB P B`, `cvtop-val` at conversions V2 defines).
* `WholeCvtEdge`: `not_bwdLive20_floatB`, `not_bwdParts20_floatB`: at builtins that interpret the
  primitives as the spec does, the per-rule obligations are false, because the 2.0 script's generic
  `$cvtop__` clauses compute at the typed `CVTOP I32 I64 (EXTEND S)` (`fires_cvtBad`) where V2 only
  traps (`pureStep_cvtBad`).
* `WholeBwdQ`: the backward recursion under a code invariant (`backward20Q_of_parts`), the
  invariant `CvtOkL` (`codeInv_cvtOk`), and `wholeStepBwdV_of_rest`: `Task.wholeStepBwdV` from
  the obligations still open (`BwdRestQ`: the vector rules of `Step_pure`, the live `Step_read`
  rules, `Step` rules 4–21).

Pass 7:

* `WholeVecEdge`: `$lanes_` has no clause and `Sim.Floats.floatIntB` does not answer it
  (`floatIntB_lanes`, `not_callDef_lanes`), so `vtestop-true` (rule 38) never fires
  (`not_body38`) and the `otherwise` of `vtestop-false` (rule 39) always holds
  (`otherwise_vtestopFalse`): the script reduces `v128.const ones; i64x2.all_true` to
  `i32.const 0` (`fires39`), V2 only to `i32.const 1` (`step_allTrue`). Hence
  `not_bwdRestQ_floatIntB : ¬ BwdRestQ CvtOkL (floatIntB P) hn P host`: the route of
  `wholeStepBwdV_of_rest` is closed.
* `WholeVecRefute`: `sstep20_of_pure` (lifting through `Step/pure`), `sstepB_allTrue`, and
  `not_wholeStepBwdV : ¬ Task.wholeStepBwdV`.
* `WholeResEdge`: `Step/memory.grow-fail` has no premise, so it fires in a frame with no memory
  (`fires20_memGrowFail`), where V2 has no step (`not_step_memGrow`):
  `not_wholeStepBwd_noRes` refutes the backward half on vector-free code without a resource
  hypothesis.
* `WholeBwdW`: the corrected target `Task.wholeStepBwdW` (`Whole.Defs`: vector-free code,
  `NoVecL`, whose named resources exist, `ResOkL`). The backward recursion under a configuration
  invariant (`CfgInv`, `bwdG_all`, `backward20G_of_parts`); the live vector rules do not fire at
  vector-free code (`not_firesPure_vec`); so `Step_pure` is discharged entirely (`pure_bwdW`) and
  `wholeStepBwdW_of_rest` reduces the target to the `Step_read` and `Step` obligations
  (`BwdRestW`), which are open.
* `WholeRestVar`: `local.get`, `global.get` (`Step_read` 7, 8), `local.set`, `global.set`
  (`Step` 4, 5) backwards at `GoodW` configurations (`bwdRead_localGet`, `bwdRead_globalGet`,
  `bwdStep_localSet`, `bwdStep_globalSet`): the lookups come from `ResOkL`, the typing from the
  rule's quantifiers (`typedV_quant`). `wholeStepBwdW_of_rest2` (`BwdRestW2`).
* `WholeRestInert`: rules with an `if` premise on `$nbytes_`, `$ibytes_`, `$vbytes_`, `$lanes_`
  or `$inv_lanes_` never fire at `floatIntB` (`not_body_inert`, `not_fires_inert`): `Step_read`
  23, 25, 27, 29, 31, 33, 35 and `Step` 12, 14, 16, 18 (`inertRead20_ok`, `inertStep20_ok`).
  `wholeStepBwdW_of_rest3` (`BwdRestW3`): what is left are the table and bulk-memory `Step_read`
  rules, `memory.size`, and `Step` rules 6–11, 13, 15, 17, 19–21.
* `WholeRestDrop`, `WholeRestTable` (round 2, track spectec20): `Step` 10 and 21 (`elem.drop`,
  `data.drop`), `Step_read` 10 (`table.get-val`), `Step` 6, 7 (`table.set-trap`, `table.set-val`)
  and `Step` 9, 20 (`table.grow-fail`, `memory.grow-fail`, at profiles that allow growth to fail)
  backwards at `GoodW` configurations. `wholeStepBwdW_of_rest4` (`BwdRestW4`).
* `WholeConstBound`: an IL-typed 2.0 `CONST I32 (% k)` has `k < 2 ^ 32` (`lt_of_typed_constI32`,
  through `instr`, `num_`, `iN`, `uN`). `WholeRestSize`: `Step_read` 11 and 36 (`table.size`,
  `memory.size`) backwards, the count bounded by the typing of the result.
  `wholeStepBwdW_of_rest5` (`BwdRestW5`).
* `WholeRestFill`, `WholeRestMemFill`: `Step_read` 13, 14, 38, 39 (`table.fill` and `memory.fill`,
  `-zero` and `-succ`) backwards: the bound read back from the `otherwise` premise
  (`otherwise_absurd`, `body_ifRule`), `n ≠ 0` from `$(n - 1)` (`pred_inv`).
  `wholeStepBwdW_of_rest6` (`BwdRestW6`).
* `WholeRestCopy`, `WholeRestInit`: `Step_read` 16, 17, 41, 42 (`table.copy`/`memory.copy`
  `-zero`, `-le`) and 20, 21 (`table.init` `-zero`, `-succ`) backwards; the `-trap` premise is a
  disjunction (`evalExp_or`). `wholeStepBwdW_of_rest7` (`BwdRestW7`).
* `WholeRestMemInit`: `Step_read` 45, 46 (`memory.init`) backwards (`byteArray_toList_eq`).
  `wholeStepBwdW_of_rest8` (`BwdRestW8`); of `Step_read` only 18 and 43 (the `-gt` rules) remain
  (`read8_left`).
* `WholeRestCopyGt`: `Step_read` 18, 43 (`table.copy-gt`, `memory.copy-gt`) backwards: `otherwise`
  is constructed for the `-le` rule (`otherwise17`, `otherwise42`, through the tag table) so that
  its body can be refuted. `wholeStepBwdW_of_rest9` (`BwdRestW9`): every `Step_pure` and
  `Step_read` rule is discharged; only `Step` 8, 11, 13, 15, 17, 19 remain (`step9_left`).
* `WholeRestStoreTrap`: `Step` 11, 13, 15, 17 (the store and vector-store trap rules) backwards;
  `w/8` is computed in `rat` (`evalExp_div8`). `wholeStepBwdW_of_rest10` (`BwdRestW10`): only the
  two `grow-succeed` rules, `Step` 8 and 19, remain.

Round 2, pass 2:

* `WholeRestGrow`: `$growtable` and `$growmemory` have one clause each, whose first premise mentions
  limit variables nothing binds, so the clause fails definitely and the call is the builtins'
  answer (`growtable20_builtin`, `growmemory20_builtin`). `floatIntB` answers neither, so `Step` 8
  and 19 never fire there (`not_fires_tableGrowSucceed`, `not_fires_memGrowSucceed`), and
  **`wholeStepBwdW : Task.wholeStepBwdW`** is proved. For these two rules the discharge is
  vacuous: at the spec's builtins the 2.0 script cannot grow a table or a memory.
* `WholeGrowAnswer`: at builtins whose growth answers are V2's (`GrowAnswers20`), `Step` 8 and 19
  are V2's `tableGrowSucceed`/`memoryGrowSucceed` backwards (`bwdStep_tableGrowSucceed`,
  `bwdStep_memGrowSucceed`); the result bounds come from the growth (`refs_lt_of_grow`,
  `pages_lt_of_grow`, `pages_of_cvt`). `wholeStepBwdW_at`: the backward half at any builtins with
  `IntB`, `FloatB`, `InertEnv` and `GrowAnswers20`.
* `WholeGrowB`: `growB P`, the spec's builtins with `$growtable`/`$growmemory` answered by V2's
  growth (well defined because `tableInstV` and `memInstV` are injective), has all four, so
  `wholeStepBwdW_growB` is the backward half at builtins where `Step` 8 and 19 can fire.
* `WholeGrow10` (1.0 route, first step): `simEnv10`; 1.0's `$growmemory` is also the builtins'
  answer (`growmemory10_builtin`), so 1.0's `memory.grow-succeed` (`Step` 11) never fires at
  `floatIntB` (`not_fires_memGrowSucceed10_floatIntB`).

Round 2, pass 3:

* `WholeGrowTyping`: every V2 table and memory instance is an IL `tableinst`/`meminst` of the 2.0
  script (`typedV_tableInst20`, `typedV_memInst20`), and the state of a typed configuration is
  typed (`typedV_state_of_typed20`).
* `WholeGrowFwd`: `Step` 8, 9, 19 and 20 fire forward at the images of V2's four growth steps
  (`fires_tableGrowSucceed`, …), at builtins answering V2's growth (`GrowCalls20`, held by `growB`).
* `WholeFwdGrow`: `Task.wholeStepGrow20` (proved, `wholeStepGrow20`): at `growB`-like builtins,
  forward on V2's growth steps from typed configurations with whole pages, backward on every
  `GoodW` configuration. `not_fwd_noCtxt`: excluding `ctxt-instrs` alone does not make the
  forward half true.
* `WholeFwdTop`: `Task.wholeStepTop20` (proved, `wholeStepTop20`): the same on a wider fragment
  `TopStep20`, adding `table.set-trap`, `table.set-val`, `elem.drop`, `data.drop` (`Step` 6, 7, 10,
  21; `fires_tableSetTrap`, …).

Round 2, pass 4:

* `WholeValTyping`: every V2 value is an IL `val` of the 2.0 script (`typedV_val20`), at every
  builtins: numbers through `NumTyped.num`, vectors through `vec_(V128) = vN($size(V128))`
  (`hasTyp_vec20`), references through `val`'s reference cases.
* `WholeFwdVar`: `Step` 4 and 5 fire forward (`fires_localSet`, `fires_globalSet`), and
  `Task.wholeStepTopVar20` (proved, `wholeStepTopVar20`) widens `Task.wholeStepTop20` to
  `TopVarStep20` (adding V2's `localSet` and `globalSet`). `drop_iff20`: `Pure.drop_iff` without
  its typing hypothesis.
* `WholeFwdVStore`: `Step` 15 and 17 (`vstore-oob`, `vstore_lane-oob`) fire forward
  (`fires_vstoreOob`, `fires_vstoreLaneOob`; `memarg`, `laneidx`, `vec_(V128)` typed), and
  `Task.wholeStepTopVS20` (proved, `wholeStepTopVS20`) widens the fragment to `TopVStep20`.
  `not_fires_vstoreVal_growLike`, `not_fires_vstoreLaneVal_growLike`: `Step` 16 and 18 never fire
  at `GrowLike20` builtins (they keep `$vbytes_`, `$ibytes_`, `$lanes_` inert;
  `not_fires_inert20`).
* `WholeCtxS` (the `StepFix` erratum route below the top of the code): `fires_topVStep20` (each
  fragment step fires one of the original `Step` 4–21), `typedV_code_of_typed20`, and
  `fwd_ctxTop20S`: from the open transfer hypotheses `StepAgreeS B` (rules 4–21 fire alike in
  `simEnv20S B`, one index later) and `TypAgreeS B` (`state`, `admininstr*`, `val*` type alike), a
  fragment step under any value prefix and suffix is a step of the corrected script.
  `Task.wholeStepCtxS20` (frozen, forward only, at `growB`) follows (`wholeStepCtxS20_of_agree`).
* `WholeCtxAgree` (pass 5): `stepAgreeS`, `typAgreeS` prove the two transfer hypotheses at every
  builtins, from `Sim20.RelFree` (the 2.0 script is relation-free away from `$instantiate`, and
  `simEnv20S B` is `simEnv20 B` with another relation table). So **`Task.wholeStepCtxS20` is
  proved** (`wholeStepCtxS20`); `fwd_ctxTop20S'` is `fwd_ctxTop20S` without the hypotheses.
* `WholeFwdS` (pass 5): the other structural rules of the erratum forward on V2 images, typing
  read in `simEnv20 B`: `fwdS_pure`/`sstepS_of_spure20` and `fwdS_read`/`sstepS_of_sread20` (a
  `Step_pure`/`Step_read` derivation of the original script is a corrected `Step`, via
  `RelFree.spure20S_iff`, `RelFree.sread20S_iff`), `fwdS_label` (`ctxt-label`) and `fwdS_frame`
  (`ctxt-frame`).
* `WholeSubjRed` (pass 5): subject reduction for the image of the fragment,
  `typed20_of_topVStep20` (the record types of `config`, `state`, `store`, `frame`, `globalinst`,
  `eleminst`, `datainst` taken apart and rebuilt, at every builtins). So
  **`Task.wholeStepCtxS20'`** (`Task.wholeStepCtxS20` without the successor hypothesis) is
  proved (`wholeStepCtxS20'`).
-/

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepValid

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.sstepB20_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.sstepB20_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwd_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwd_of_parts

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_fwd_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_fwd_unreachable

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwd_of_live' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwd_of_live

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_bwdLive20_floatB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_bwdLive20_floatB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdV_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdV_of_rest

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.pureDone_bwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.pureDone_bwd

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_bwdRestQ_floatIntB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_bwdRestQ_floatIntB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepBwdV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepBwdV

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepBwd_noRes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_wholeStepBwd_noRes

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest3

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest4

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest5

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest6

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest7

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest8

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest9

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_of_rest10

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_at

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_growB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepBwdW_growB

/--
info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_memGrowSucceed10_floatIntB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_memGrowSucceed10_floatIntB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_tableInst20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_tableInst20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_memInst20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_memInst20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_state_of_typed20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_state_of_typed20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableGrowSucceed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableGrowSucceed

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableGrowFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableGrowFail

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_memGrowSucceed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_memGrowSucceed

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_memGrowFail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_memGrowFail

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_growStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_growStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepGrow20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepGrow20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_fwd_noCtxt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_fwd_noCtxt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableSetTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableSetTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableSetVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_tableSetVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_elemDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_elemDrop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_dataDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_dataDrop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTop20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTop20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_val20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_val20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.hasTyp_vec20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.hasTyp_vec20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_localSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_localSet

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_globalSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_globalSet

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topVarStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topVarStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTopVar20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTopVar20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreOob

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreLaneOob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreLaneOob

/--
info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_vstoreVal_growLike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_vstoreVal_growLike

/--
info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_vstoreLaneVal_growLike' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_fires_vstoreLaneVal_growLike

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topVStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_topVStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTopVS20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepTopVS20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_topVStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_topVStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_code_of_typed20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_code_of_typed20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_ctxTop20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_ctxTop20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20_of_agree

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.stepAgreeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.stepAgreeS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typAgreeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typAgreeS

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_pure

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_label

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdS_frame

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typed20_of_topVStep20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typed20_of_topVStep20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepCtxS20'

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_adminLabel20_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_adminLabel20_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_adminFrame20_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_adminFrame20_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_nest20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_nest20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepNest20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepNest20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admin_val20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admin_val20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.spure_of_pureFrag20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.spure_of_pureFrag20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_pure

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_read

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_typedV_store20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_typedV_store20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_typed20_nestStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_typed20_nestStore

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_typed20_storeStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_typed20_storeStep

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.vbytes20_vbytesB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.vbytes20_vbytesB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20V

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admin_iff_instr20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admin_iff_instr20

/--
info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admins_expression20_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_admins_expression20_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.spure_of_pureFrag20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.spure_of_pureFrag20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_succ_pureFrag20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_succ_pureFrag20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_pureB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_pureB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_call

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.laneCalls20_laneB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.laneCalls20_laneB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.callDef_jsize20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.callDef_jsize20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_dim20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_dim20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreLaneVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_vstoreLaneVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_vstoreLaneVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_vstoreLaneVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20L

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storeNumTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storeNumTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storeNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storeNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storePackTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storePackTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storePackVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_storePackVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.nbytes20_storeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.nbytes20_storeB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepStoreTop20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepStoreTop20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_good20S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_good20S

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_invoke' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.plain20_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.step_pendHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.step_pendHead

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_ctx

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_label

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.tail20_frame

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover_tail

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.pureStep_cover_plain

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_valType20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_valType20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.callDef_blocktype20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.callDef_blocktype20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_block20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_block20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loop20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loop20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_block

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20BL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20BL

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.evalExp_default20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.evalExp_default20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_funcInst_parts20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_funcInst_parts20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_body_of_func20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.typedV_body_of_func20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callAddr20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callAddr20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_callAddr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_callAddr

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20C

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.adminOk_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.adminOk_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.adminOk_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.adminOk_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.cover20C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.cover20C

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_good20C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwd_good20C

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.good20C_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.good20C_steps

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.good20C_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.good20C_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loadNumTrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loadNumTrap

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loadNumVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_loadNumVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fwdBase20_load

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20D

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callIndirectCall20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callIndirectCall20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20E

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.not_callIndBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.not_callIndBody

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.otherwise4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.otherwise4

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callIndirectTrap20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.fires_callIndirectTrap20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Silmaril.Wasm.SpecTec.Sim20.Whole.wholeStepFwd20F
