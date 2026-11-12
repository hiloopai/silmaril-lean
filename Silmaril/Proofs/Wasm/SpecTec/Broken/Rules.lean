module

public import Silmaril.Proofs.Wasm.SpecTec.Broken.Fuel
public import Silmaril.Wasm.SpecTec.Scripts.Thms

/-!
# Rules that never fire, in the generated original and fixed wasm-3.0 scripts

Each rule below is the stated rule of `Step` or `Step_read` in the generated script (checked by
`rfl` on the fixed script and by transport along `wasm30_original_eq` on the original), and fires
at no value (`Equiv/Exec*.lean`; those proofs hold at every environment).  The errata do not
touch these relations, and the `fixed` facts confirm it rule by rule.
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Validation
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 8000000
set_option maxHeartbeats 8000000

/-- Rule provenance in the generated original, from the imported stream. -/
theorem hasRuleAt_original {rel : IL.Id} {k : Nat} {r : Rule}
    (h : HasRuleAt (envOfScript Specs.wasm30) rel "%~>%" k r) :
    HasRuleAt Wasm30.envOriginal rel "%~>%" k r := by
  rw [Wasm30.envOriginal, wasm30_original_eq]; exact h

/-- `Step/tableGrowSucceed` (rule 15) never fires in the original. -/
theorem ruleDead_tableGrowSucceed_original : RuleDead Wasm30.original "Step" 15 ExecStepRules.tableGrowSucceedRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.tableGrowSucceed,
    fun _ => ExecStepRules.not_ruleFires_tableGrowSucceed_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_tableGrowSucceed_fixed : RuleDead Wasm30.fixed "Step" 15 ExecStepRules.tableGrowSucceedRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_tableGrowSucceed_pinned⟩

/-- `Step/memoryGrowSucceed` (rule 26) never fires in the original. -/
theorem ruleDead_memoryGrowSucceed_original : RuleDead Wasm30.original "Step" 26 ExecStepRules.memoryGrowSucceedRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.memoryGrowSucceed,
    fun _ => ExecStepRules.not_ruleFires_memoryGrowSucceed_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_memoryGrowSucceed_fixed : RuleDead Wasm30.fixed "Step" 26 ExecStepRules.memoryGrowSucceedRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_memoryGrowSucceed_pinned⟩

/-- `Step/storeNumVal` (rule 19) never fires in the original. -/
theorem ruleDead_storeNumVal_original : RuleDead Wasm30.original "Step" 19 ExecStepRules.storeNumValRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.storeNumVal,
    fun _ => ExecStepRules.not_ruleFires_storeNumVal_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_storeNumVal_fixed : RuleDead Wasm30.fixed "Step" 19 ExecStepRules.storeNumValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_storeNumVal_pinned⟩

/-- `Step/storePackVal` (rule 21) never fires in the original. -/
theorem ruleDead_storePackVal_original : RuleDead Wasm30.original "Step" 21 ExecStepRules.storePackValRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.storePackVal,
    fun _ => ExecStepRules.not_ruleFires_storePackVal_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_storePackVal_fixed : RuleDead Wasm30.fixed "Step" 21 ExecStepRules.storePackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_storePackVal_pinned⟩

/-- `Step/vstoreVal` (rule 23) never fires in the original. -/
theorem ruleDead_vstoreVal_original : RuleDead Wasm30.original "Step" 23 ExecStepRules.vstoreValRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.vstoreVal,
    fun _ => ExecStepRules.not_ruleFires_vstoreVal_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vstoreVal_fixed : RuleDead Wasm30.fixed "Step" 23 ExecStepRules.vstoreValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_vstoreVal_pinned⟩

/-- `Step/vstoreLaneVal` (rule 25) never fires in the original. -/
theorem ruleDead_vstoreLaneVal_original : RuleDead Wasm30.original "Step" 25 ExecStepRules.vstoreLaneValRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.vstoreLaneVal,
    fun _ => ExecStepRules.not_ruleFires_vstoreLaneVal_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vstoreLaneVal_fixed : RuleDead Wasm30.fixed "Step" 25 ExecStepRules.vstoreLaneValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_vstoreLaneVal_pinned⟩

/-- `Step/structSetStruct` (rule 31) never fires in the original. -/
theorem ruleDead_structSetStruct_original : RuleDead Wasm30.original "Step" 31 ExecStepRules.structSetStructRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.structSetStruct,
    fun _ => ExecStepRules.not_ruleFires_structSetStruct_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_structSetStruct_fixed : RuleDead Wasm30.fixed "Step" 31 ExecStepRules.structSetStructRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_structSetStruct_pinned⟩

/-- `Step/arraySetArray` (rule 35) never fires in the original. -/
theorem ruleDead_arraySetArray_original : RuleDead Wasm30.original "Step" 35 ExecStepRules.arraySetArrayRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.arraySetArray,
    fun _ => ExecStepRules.not_ruleFires_arraySetArray_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_arraySetArray_fixed : RuleDead Wasm30.fixed "Step" 35 ExecStepRules.arraySetArrayRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_arraySetArray_pinned⟩

/-- `Step/throw` (rule 10) never fires in the original. -/
theorem ruleDead_throw_original : RuleDead Wasm30.original "Step" 10 ExecStepRules.throwRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.throw,
    fun _ => ExecStepRules.not_ruleFires_throw_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_throw_fixed : RuleDead Wasm30.fixed "Step" 10 ExecStepRules.throwRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_throw_pinned⟩

/-- `Step/structNew` (rule 29) never fires in the original. -/
theorem ruleDead_structNew_original : RuleDead Wasm30.original "Step" 29 ExecStepRules.structNewRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.structNew,
    fun _ => ExecStepRules.not_ruleFires_structNew_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_structNew_fixed : RuleDead Wasm30.fixed "Step" 29 ExecStepRules.structNewRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_structNew_pinned⟩

/-- `Step/arrayNewFixed` (rule 32) never fires in the original. -/
theorem ruleDead_arrayNewFixed_original : RuleDead Wasm30.original "Step" 32 ExecStepRules.arrayNewFixedRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.arrayNewFixed,
    fun _ => ExecStepRules.not_ruleFires_arrayNewFixed_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_arrayNewFixed_fixed : RuleDead Wasm30.fixed "Step" 32 ExecStepRules.arrayNewFixedRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_arrayNewFixed_pinned⟩

/-- `Step/callRefFunc` (rule 7) never fires in the original. -/
theorem ruleDead_callRefFunc_original : RuleDead Wasm30.original "Step" 7 ExecStepRules.callRefFuncRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.callRefFunc,
    fun _ => ExecStepRules.not_ruleFires_callRefFunc_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_callRefFunc_fixed : RuleDead Wasm30.fixed "Step" 7 ExecStepRules.callRefFuncRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_callRefFunc_pinned⟩

/-- `Step/callRefHostfuncRes` (rule 8) never fires in the original. -/
theorem ruleDead_callRefHostfuncRes_original : RuleDead Wasm30.original "Step" 8 ExecStepRules.callRefHostfuncResRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.callRefHostfuncRes,
    fun _ => ExecStepRules.not_ruleFires_callRefHostfuncRes_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_callRefHostfuncRes_fixed : RuleDead Wasm30.fixed "Step" 8 ExecStepRules.callRefHostfuncResRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_callRefHostfuncRes_pinned⟩

/-- `Step/callRefHostfuncDiv` (rule 9) never fires in the original. -/
theorem ruleDead_callRefHostfuncDiv_original : RuleDead Wasm30.original "Step" 9 ExecStepRules.callRefHostfuncDivRule :=
  ⟨hasRuleAt_original ExecStepRules.hasStepRules_wasm30.callRefHostfuncDiv,
    fun _ => ExecStepRules.not_ruleFires_callRefHostfuncDiv_pinned⟩

/-- …nor in the fixed script. -/
theorem ruleDead_callRefHostfuncDiv_fixed : RuleDead Wasm30.fixed "Step" 9 ExecStepRules.callRefHostfuncDivRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_callRefHostfuncDiv_pinned⟩

/-- `Step_read/block` (rule 0) never fires in the original. -/
theorem ruleDead_block_original : RuleDead Wasm30.original "Step_read" 0 ExecRead.blockRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.block, fun _ => ExecReadControl.not_ruleFires_block⟩

/-- …nor in the fixed script. -/
theorem ruleDead_block_fixed : RuleDead Wasm30.fixed "Step_read" 0 ExecRead.blockRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_block⟩

/-- `Step_read/loop` (rule 1) never fires in the original. -/
theorem ruleDead_loop_original : RuleDead Wasm30.original "Step_read" 1 ExecRead.loopRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.loop, fun _ => ExecReadControl.not_ruleFires_loop⟩

/-- …nor in the fixed script. -/
theorem ruleDead_loop_fixed : RuleDead Wasm30.fixed "Step_read" 1 ExecRead.loopRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_loop⟩

/-- `Step_read/tryTable` (rule 22) never fires in the original. -/
theorem ruleDead_tryTable_original : RuleDead Wasm30.original "Step_read" 22 ExecRead.tryTableRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.tryTable, fun _ => ExecReadControl.not_ruleFires_tryTable⟩

/-- …nor in the fixed script. -/
theorem ruleDead_tryTable_fixed : RuleDead Wasm30.fixed "Step_read" 22 ExecRead.tryTableRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_tryTable⟩

/-- `Step_read/returnCallRefFrameAddr` (rule 11) never fires in the original. -/
theorem ruleDead_returnCallRefFrameAddr_original : RuleDead Wasm30.original "Step_read" 11 ExecRead.returnCallRefFrameAddrRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.returnCallRefFrameAddr, fun _ => ExecReadControl.not_ruleFires_returnCallRefFrameAddr⟩

/-- …nor in the fixed script. -/
theorem ruleDead_returnCallRefFrameAddr_fixed : RuleDead Wasm30.fixed "Step_read" 11 ExecRead.returnCallRefFrameAddrRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_returnCallRefFrameAddr⟩

/-- `Step_read/tableSize` (rule 27) never fires in the original. -/
theorem ruleDead_tableSize_original : RuleDead Wasm30.original "Step_read" 27 ExecRead.tableSizeRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.tableSize, fun _ => ExecReadTable.not_ruleFires_tableSize⟩

/-- …nor in the fixed script. -/
theorem ruleDead_tableSize_fixed : RuleDead Wasm30.fixed "Step_read" 27 ExecRead.tableSizeRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadTable.not_ruleFires_tableSize⟩

/-- `Step_read/memorySize` (rule 52) never fires in the original. -/
theorem ruleDead_memorySize_original : RuleDead Wasm30.original "Step_read" 52 ExecRead.memorySizeRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.memorySize, fun _ => ExecReadMemory.not_ruleFires_memorySize⟩

/-- …nor in the fixed script. -/
theorem ruleDead_memorySize_fixed : RuleDead Wasm30.fixed "Step_read" 52 ExecRead.memorySizeRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_memorySize⟩

/-- `Step_read/loadPackVal` (rule 41) never fires in the original. -/
theorem ruleDead_loadPackVal_original : RuleDead Wasm30.original "Step_read" 41 ExecRead.loadPackValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.loadPackVal, fun _ => ExecReadMemory.not_ruleFires_loadPackVal⟩

/-- …nor in the fixed script. -/
theorem ruleDead_loadPackVal_fixed : RuleDead Wasm30.fixed "Step_read" 41 ExecRead.loadPackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_loadPackVal⟩

/-- `Step_read/vloadPackVal` (rule 45) never fires in the original. -/
theorem ruleDead_vloadPackVal_original : RuleDead Wasm30.original "Step_read" 45 ExecRead.vloadPackValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.vloadPackVal, fun _ => ExecReadMemory.not_ruleFires_vloadPackVal⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vloadPackVal_fixed : RuleDead Wasm30.fixed "Step_read" 45 ExecRead.vloadPackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadPackVal⟩

/-- `Step_read/vloadSplatVal` (rule 47) never fires in the original. -/
theorem ruleDead_vloadSplatVal_original : RuleDead Wasm30.original "Step_read" 47 ExecRead.vloadSplatValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.vloadSplatVal, fun _ => ExecReadMemory.not_ruleFires_vloadSplatVal⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vloadSplatVal_fixed : RuleDead Wasm30.fixed "Step_read" 47 ExecRead.vloadSplatValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadSplatVal⟩

/-- `Step_read/vloadZeroVal` (rule 49) never fires in the original. -/
theorem ruleDead_vloadZeroVal_original : RuleDead Wasm30.original "Step_read" 49 ExecRead.vloadZeroValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.vloadZeroVal, fun _ => ExecReadMemory.not_ruleFires_vloadZeroVal⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vloadZeroVal_fixed : RuleDead Wasm30.fixed "Step_read" 49 ExecRead.vloadZeroValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadZeroVal⟩

/-- `Step_read/vloadLaneVal` (rule 51) never fires in the original. -/
theorem ruleDead_vloadLaneVal_original : RuleDead Wasm30.original "Step_read" 51 ExecRead.vloadLaneValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.vloadLaneVal, fun _ => ExecReadMemory.not_ruleFires_vloadLaneVal⟩

/-- …nor in the fixed script. -/
theorem ruleDead_vloadLaneVal_fixed : RuleDead Wasm30.fixed "Step_read" 51 ExecRead.vloadLaneValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadLaneVal⟩

end Silmaril.Wasm.SpecTec.Broken
