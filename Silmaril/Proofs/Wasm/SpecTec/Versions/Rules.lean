module

public import Silmaril.Wasm.SpecTec.Versions.Defs
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-!
# Rules that never fire, on the main wasm-3.0 script

Of the 25 rules `Silmaril.Wasm.SpecTec.Broken` proves dead in the pinned script, 18 are unchanged on
`WebAssembly/spec@e7a9df7c` (same name, same index, same printed rule) and are proved dead there
below: the rule provenance is a kernel `rfl` against the generated main script and the deadness
proof is the pinned, environment-generic one.  The other 7 (`Step` rules 7, 8, 9, 10, 29, 32 and
`Step_read` rule 11: `call_ref-func`, `call_ref-hostfunc-res`/`-div`, `throw`, `struct.new`,
`array.new_fixed`, `return_call_ref-frame-addr`) were rewritten upstream when the auxiliary state
accessors were simplified (`$funcinst(z)[a]` became `$s(z).FUNCS[a]`, and so on).  Their `if`
premises still read as bindings (`if $s(z).FUNCS[a] = fi`, `if a = |$s(z).EXNS|`), so the cause
of their deadness is unchanged, but they are **not re-proved** here.
-/

public section

namespace Silmaril.Wasm.SpecTec.Versions

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Validation
open Silmaril.Wasm.SpecTec.Broken

set_option maxRecDepth 8000000
set_option maxHeartbeats 8000000

/-- `Step` rule 15 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_tableGrowSucceed_main : RuleDead Main.Wasm30.original "Step" 15 ExecStepRules.tableGrowSucceedRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_tableGrowSucceed_pinned⟩

/-- `Step` rule 26 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_memoryGrowSucceed_main : RuleDead Main.Wasm30.original "Step" 26 ExecStepRules.memoryGrowSucceedRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_memoryGrowSucceed_pinned⟩

/-- `Step` rule 19 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_storeNumVal_main : RuleDead Main.Wasm30.original "Step" 19 ExecStepRules.storeNumValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_storeNumVal_pinned⟩

/-- `Step` rule 21 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_storePackVal_main : RuleDead Main.Wasm30.original "Step" 21 ExecStepRules.storePackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_storePackVal_pinned⟩

/-- `Step` rule 23 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vstoreVal_main : RuleDead Main.Wasm30.original "Step" 23 ExecStepRules.vstoreValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_vstoreVal_pinned⟩

/-- `Step` rule 25 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vstoreLaneVal_main : RuleDead Main.Wasm30.original "Step" 25 ExecStepRules.vstoreLaneValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_vstoreLaneVal_pinned⟩

/-- `Step` rule 31 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_structSetStruct_main : RuleDead Main.Wasm30.original "Step" 31 ExecStepRules.structSetStructRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_structSetStruct_pinned⟩

/-- `Step` rule 35 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_arraySetArray_main : RuleDead Main.Wasm30.original "Step" 35 ExecStepRules.arraySetArrayRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecStepRules.not_ruleFires_arraySetArray_pinned⟩

/-- `Step_read` rule 0 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_block_main : RuleDead Main.Wasm30.original "Step_read" 0 ExecRead.blockRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_block⟩

/-- `Step_read` rule 1 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_loop_main : RuleDead Main.Wasm30.original "Step_read" 1 ExecRead.loopRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_loop⟩

/-- `Step_read` rule 22 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_tryTable_main : RuleDead Main.Wasm30.original "Step_read" 22 ExecRead.tryTableRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadControl.not_ruleFires_tryTable⟩

/-- `Step_read` rule 27 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_tableSize_main : RuleDead Main.Wasm30.original "Step_read" 27 ExecRead.tableSizeRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadTable.not_ruleFires_tableSize⟩

/-- `Step_read` rule 52 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_memorySize_main : RuleDead Main.Wasm30.original "Step_read" 52 ExecRead.memorySizeRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_memorySize⟩

/-- `Step_read` rule 41 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_loadPackVal_main : RuleDead Main.Wasm30.original "Step_read" 41 ExecRead.loadPackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_loadPackVal⟩

/-- `Step_read` rule 45 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vloadPackVal_main : RuleDead Main.Wasm30.original "Step_read" 45 ExecRead.vloadPackValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadPackVal⟩

/-- `Step_read` rule 47 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vloadSplatVal_main : RuleDead Main.Wasm30.original "Step_read" 47 ExecRead.vloadSplatValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadSplatVal⟩

/-- `Step_read` rule 49 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vloadZeroVal_main : RuleDead Main.Wasm30.original "Step_read" 49 ExecRead.vloadZeroValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadZeroVal⟩

/-- `Step_read` rule 51 is unchanged on main, and still fires at nothing. -/
theorem ruleDead_vloadLaneVal_main : RuleDead Main.Wasm30.original "Step_read" 51 ExecRead.vloadLaneValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, fun _ => ExecReadMemory.not_ruleFires_vloadLaneVal⟩

end Silmaril.Wasm.SpecTec.Versions
