module

public import Silmaril.Proofs.Wasm.Dataflow.Litmus.Trap
public import Silmaril.Proofs.Wasm.Dataflow.Litmus.RelBase
public import Silmaril.Proofs.Wasm.Dataflow.Litmus.ThrowRef
public import Silmaril.Wasm.Dataflow.Dce.Defs

/-!
# Litmus programs for the Wasm dataflow DCE: theorems

The three refuted statements (proofs in `Silmaril.Proofs.Wasm.Dataflow.Litmus.*`):

* `RelBase.not_step_sim_relBase`: the fused step simulation is false for `RelBase`;
* `Trap.not_step_sim`: it is false for `Rel` as well (`Trap.source_step`: the
  counterexample is reachable from fragment source code);
* `ThrowRef.not_erase_step_sim`: an earlier simulation is false for `OldERel`;
  `ThrowRef.repaired_counterexample` and `repaired_label` check that `ERel` closes it.

Statement checks, evaluated by `decide`: a dead `local.set` and its removable producer are
deleted (`ex_deadSet`), a live `local.set` is kept (`ex_liveSet`), the locals that the loop
body reads before writing them are live at the loop head (`ex_loop_live`) and a local the
body writes before every read is not (`ex_loop_dead`), one fused
pass is not idempotent (`ex_not_idempotent`, the course's "successive iterations may yield
further improvements") while `dce2` reaches the same result in one run (`ex_dce2`), and the
example programs are fragment code, so `dce2_result` applies to them (`ex_frag`).
-/

@[expose] public section

namespace Silmaril.Wasm.Dataflow.Litmus

theorem ex_deadSet : (dce deadSet).length = 1 := by decide

theorem ex_liveSet : (dce liveSet).length = 3 := by decide

theorem ex_loop_live : (liveEntry loopEx).mem 0 = true ∧ (liveEntry loopEx).mem 1 = true := by
  decide

theorem ex_loop_dead : (liveEntry loopEx).mem 2 = false := by decide

theorem ex_not_idempotent : (dce deadTee).length = 2 ∧ (dce (dce deadTee)).length = 0 := by
  decide

theorem ex_dce2 : (dce2 deadSet).length = 1 ∧ dce2 deadTee = [] := by decide

theorem ex_frag : fragSeq deadSet = true ∧ fragSeq liveSet = true ∧ fragSeq loopEx = true ∧
    fragSeq deadTee = true := by
  decide

end Silmaril.Wasm.Dataflow.Litmus
