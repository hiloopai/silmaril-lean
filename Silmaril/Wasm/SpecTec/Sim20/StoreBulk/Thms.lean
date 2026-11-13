module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkBase
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkNest
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkRun
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkCopy
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkInit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTable
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkWit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkInv
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTCopy
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkTInit
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkWit2
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkFT
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkUtf8
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkUtf8Neg

/-!
# The memory bulk instructions and `table.fill` inside the 2.0 forward invariant

Namespace `Silmaril.Wasm.SpecTec.Sim20.StoreBulk`; see `docs/projects/spectec/README.md`, "fwd20
".

* `StoreBulkCode`: `bulkOkI`, `ctrlOkB`, `okB` (round 5's `okD` with `memory.fill` at every
  depth), `StoreOkB`, and **`typedT_of_eBL`**, **`typedT_state_of_erasedB`**: typing in
  `simEnv20T` from the deep erasure, which keeps `memory.fill`.
* `StoreBulkBase`: `MemFillFwd`, `BaseB`, **`cover20B`**, `MemsSmall`, **`okB_step`**.
* `StoreBulkNest`: **`fwd_nestB`**, with `memory.fill` fired 's rule-level lemmas and
  the erased successor of `-succ` typed in `simEnv20` (`typedE_fillSucc`).
* `StoreBulkRun`: **`Good20B`**, **`fwd_good20B`**, **`good20B_steps`**, `runT_good20B`,
  `typed20T_of_good20B`, **`good20B_of_good20F`**, `good20B_invoke`, and witnesses outside
  `Good20F` (`good20B_beyond_good20F`, `sstep_callFillCfg`).
* `StoreBulkWit`: `memory.copy-le` and `memory.init-succ` steps from configurations outside
  `Good20F`, each a step of `simEnv20T` (`sstep_copyCfg`, `sstep_initCfg`); likewise
  `table.fill-succ` (`sstep_tfillCfg`).
* `StoreBulkInv`: every global and element instance typed in `simEnv20` (`typedV_globalInst20`,
  `typedV_elemInst20`); **`typedV_erasedState_of`** and **`good20B_invoke_of`**: at invocation,
  `Good20B` needs only `InvokeTy` (module instances, function types and erased bodies typed),
  `StoreOkB` and `StoreSmall`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedT_of_eBL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_of_eBL

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedT_state_of_erasedB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedT_state_of_erasedB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.cover20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cover20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.okB_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms okB_step

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.fwd_nestB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_nestB

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.fwd_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwd_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.runT_good20B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runT_good20B

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.good20B_of_good20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20B_of_good20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.good20B_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20B_invoke

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.good20B_beyond_good20F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20B_beyond_good20F

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_callFillCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_callFillCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_memCopyGt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_memCopyGt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_memInitSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_memInitSucc

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_copyCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_copyCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_initCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_initCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedV_globalInst20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_globalInst20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedV_elemInst20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_elemInst20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.good20B_invoke_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20B_invoke_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_tableSetVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_tableSetVal

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_tableFillSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_tableFillSucc

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_tfillCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_tfillCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_tableCopyGt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_tableCopyGt

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_tableInitSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_tableInitSucc

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_elemDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_elemDrop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.firesT_dataDrop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firesT_dataDrop

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.fwdB_tcopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdB_tcopy

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.fwdB_tinit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fwdB_tinit

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_tcopyCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_tcopyCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_tinitCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_tinitCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_edropCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_edropCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.sstep_ddropCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sstep_ddropCfg

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedV_funcType20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_funcType20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedV_moduleInstE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_moduleInstE

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.invokeTy_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeTy_of

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.good20B_invoke_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms good20B_invoke_ok

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.hasTyp_name20U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_name20U

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.typedV_moduleInst_utf8Env20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typedV_moduleInst_utf8Env20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.tryClauses_utf8_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tryClauses_utf8_20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.not_hasTyp_name_single20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_hasTyp_name_single20

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.not_typedV_moduleInst20_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_typedV_moduleInst20_single

/-- info: 'Silmaril.Wasm.SpecTec.Sim20.StoreBulk.not_good20B_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_good20B_single

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
