module

public import Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness.Defs
public import Silmaril.Compiler.Native.Optimize.LambdaSSA.SelectedSoundness.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Context.Thms
/-! Actual selected/caller refinement from low/slot-related partial frames,
with genuine function membership bounds and actual versionFunc block lookup. -/
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness
open Silmaril.Compile Silmaril.Machine
open Validation.PureSoundness

/-- Actual function membership and actual successful LambdaSSA selection
supply all bounds/admissions/checks for refinement from a different incoming
partial frame, with scratch differences already present. -/
theorem optimize_contextual {function : Mir.Func} {source candidate : Mir.Block} {count : Nat}
    (member : source ∈ function.blocks.toList)
    (selected : optimize? (freshBase function) source = some (candidate, count))
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal := by
  obtain ⟨sourceAdmitted, candidateAdmitted, checked⟩ := OptimizerAdmission.optimize_admitted selected
  exact Validation.Context.function_checked_contextual member sourceAdmitted candidateAdmitted checked
    calls sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed

/-- The real caller, including actual selected LambdaSSA, checked local SSA
fallback and identity fallback, refines from a different incoming partial
frame. Source read bounds come only from actual function membership. -/
theorem roundTripBlock_contextual {function : Mir.Func} {source : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (admitted : Validation.Lists.Admitted source.instrs.toList) (cfg : Config)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls (roundTripBlock cfg (freshBase function) source)
        candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := Validation.Context.block_transport
    calls (freshBase function) source admitted (Validation.Context.freshBase_reads member)
      sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := SelectedSoundness.roundTripBlock_preserves
    cfg (freshBase function) source admitted calls candidateInput transportedFinal memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩

/-- Actual versionFunc maps each original block at exactly the same array
index to the real block caller with the original function's freshBase. -/
theorem versionFunc_block {function : Mir.Func} {source : Mir.Block} {index : Nat}
    (found : function.blocks[index]? = some source) (cfg : Config) :
    (versionFunc cfg function).blocks[index]? = some (roundTripBlock cfg (freshBase function) source) := by
  simp only [versionFunc, Array.getElem?_map, found, Option.map_some]

/-- A real source lookup supplies membership and the actual transformed
function lookup. Only source execution and initial low/slot agreement are
needed to derive the mapped block's execution from its own incoming frame. -/
theorem versionFunc_block_contextual {function : Mir.Func} {source : Mir.Block} {index : Nat}
    (found : function.blocks[index]? = some source)
    (admitted : Validation.Lists.Admitted source.instrs.toList) (cfg : Config)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidate candidateFinal,
      (versionFunc cfg function).blocks[index]? = some candidate ∧
      BlockExec calls candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal := by
  have member : source ∈ function.blocks.toList := List.mem_of_getElem? (by
    simpa only [Array.getElem?_toList] using found)
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := roundTripBlock_contextual member admitted cfg
    calls sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  exact ⟨roundTripBlock cfg (freshBase function) source, candidateFinal, versionFunc_block found cfg,
    candidateRun, candidateAgree⟩

end Silmaril.Compiler.Native.Optimize.LambdaSSA.ContextualSoundness
