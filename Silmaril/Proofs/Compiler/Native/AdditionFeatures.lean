module

public import Silmaril.Compiler.Native.Emit.AdditionFeatures.Defs
public import Silmaril.Compiler.Native.Emit.AdditionFetched.Thms
public import Silmaril.X86.FetchTrace.Features.Thms
public import Silmaril.Compiler.Native.Correctness.Execution.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.AdditionFeatures
open Silmaril Silmaril.X86
open Silmaril.X86
open Silmaril.Machine.X86.Decompile.Features (lift)
set_option maxRecDepth 8192
set_option maxHeartbeats 300000

/-- Every actual selected addition instruction uses ordinary integer feature
requirements; this is proved from syntax independently of any execution. -/
theorem retiring_admitted (left right : Word) :
    FetchTrace.Features.Admitted (AdditionFetched.retiringInstructions left right) := by
  simp [FetchTrace.Features.Admitted, AdditionFetched.retiringInstructions,
    AdditionFunction.instructions, Prologue.Plan.activate,
    Prologue.Plan.instructions, Prologue.adjust, Prologue.frameInstructions,
    AdditionBody.instructions, AdditionBody.operations, Scalar.Operation.instructions,
    Epilogue.instructions, Features.baseRequirement]

/-- The existing native baseline Features dispatcher executes the actual
canonical image from independent entry, preserving arbitrary extended state.
No Features step/run/result premise is supplied. -/
theorem execute (initial : Features.MState) (left right exit : Word) (entry : Entry initial left right exit) :
    ∃ beforeRet final,
      Features.run Features.FeatureSet.baseline64 [Features.floatExt, Features.Fpu.ext] exit 35 initial =
        some (lift initial.state beforeRet) ∧
      Correctness.step exit (lift initial.state beforeRet) = .returned (lift initial.state final) ∧
      AdditionFunction.Ready initial.toBase final left right exit ∧
      Ext.Loaded final.memory initial.state.core.rip (AdditionFunction.code left right) := by
  obtain ⟨beforeRet, final, trace, ret, ready⟩ := AdditionFetched.decoded_trace initial.toBase left right exit entry.function
  have loaded : Ext.Loaded initial.memory initial.state.core.rip
      ([] ++ FetchTrace.code (AdditionFetched.retiringInstructions left right) ++ Ext.encode .ret) := by
    simpa only [List.nil_append, ← AdditionFetched.code_split, Features.MState.toBase] using entry.loaded
  have disjoint : FetchTrace.Disjoint initial.state.core.rip
      ([] ++ FetchTrace.code (AdditionFetched.retiringInstructions left right) ++ Ext.encode .ret)
      (AdditionFunction.footprint (initial.state.core.read .rsp)) := by
    simpa only [List.nil_append, ← AdditionFetched.code_split, Features.MState.toBase] using entry.disjoint
  obtain ⟨runs, beforeLoaded⟩ := FetchTrace.Features.execute trace (retiring_admitted left right) initial.state
    Features.FeatureSet.baseline64 [Features.floatExt, Features.Fpu.ext] exit initial.state.core.rip []
    (Ext.encode .ret) loaded (by simp [Features.MState.toBase]) disjoint
  have image : Ext.Loaded beforeRet.memory initial.state.core.rip (AdditionFunction.code left right) := by
    simpa only [List.nil_append, ← AdditionFetched.code_split] using beforeLoaded
  have pc : beforeRet.core.rip = initial.state.core.rip + BitVec.ofNat 64 135 := by
    simpa only [AdditionFetched.retiring_bytes, Features.MState.toBase] using trace.pc
  have fits : 135 + 1 ≤ (AdditionFunction.code left right).length := by rw [AdditionFunction.code_length]
  have decoded : Ext.decode (((AdditionFunction.code left right).drop 135).take 1) = some (.ret, 1) := by
    have retLength : (Ext.encode .ret).length = 1 := rfl
    have exactSlice := FetchTrace.decode_at (FetchTrace.code (AdditionFetched.retiringInstructions left right)) [] .ret
    simpa only [List.append_nil, ← AdditionFetched.code_split, AdditionFetched.retiring_bytes, retLength] using exactSlice
  have returned : Ext.step exit beforeRet = .returned final :=
    Ext.step_returned_of_loaded image pc fits decoded ret ready.returned.pc
  have featureReturn := FetchTrace.Features.returned_of_loaded initial.state Features.FeatureSet.baseline64
    [Features.floatExt, Features.Fpu.ext] image pc fits decoded returned
  refine ⟨beforeRet, final, ?_, featureReturn, ready, ?_⟩
  · simpa only [AdditionFetched.retiring_count, lift, Features.MState.toBase, Features.State.setCore] using runs
  · exact FetchTrace.loaded_after entry.loaded ready.frame entry.disjoint

/-- Actual bounded source lowering and complete native Features execution
meet at the existing limited INTEGER-state SysV signed32 result boundary. -/
theorem compile_execute (left right : Int) (bounded : Correctness.AdditionSource.Bounds left right)
    (tag : String) (initial : Features.MState) (exit : Word)
    (entry : Entry initial (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit) :
    Lower.compile tag (Correctness.AdditionSource.program left right) =
      .ok (Correctness.AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) ∧
    ∃ beforeRet final,
      Features.run Features.FeatureSet.baseline64 [Features.floatExt, Features.Fpu.ext] exit 35 initial =
        some (lift initial.state beforeRet) ∧
      Correctness.step exit (lift initial.state beforeRet) = .returned (lift initial.state final) ∧
      AdditionFunction.Ready initial.toBase final (BitVec.ofInt 64 left) (BitVec.ofInt 64 right) exit ∧
      C.Api.SysV.ResultAt final (some .int32) ((BitVec.ofInt 64 (left + right)).setWidth 32) := by
  obtain ⟨beforeRet, final, runs, returned, ready, _⟩ := execute initial _ _ exit entry
  exact ⟨Correctness.AdditionLower.compile left right bounded tag, beforeRet, final, runs, returned,
    ready, ready.addition_int32 left right bounded⟩

/-- Every complete native Features observation is the single actual returned
state. All native stopped outcomes and divergence remain in the model and are
excluded by derived execution, rather than filtered from its definition. -/
theorem behavior (initial : Features.MState) (left right exit : Word) (entry : Entry initial left right exit) :
    ∃ final, AdditionFunction.Ready initial.toBase final left right exit ∧
      ∀ observation, Correctness.Realises exit initial observation ↔ observation = .returned (lift initial.state final) := by
  obtain ⟨beforeRet, final, runs, returned, ready, _⟩ := execute initial left right exit entry
  exact ⟨final, ready, Correctness.Execution.realises_iff_returned_of_run runs returned⟩

/-- Actual feature dispatch preserves ZMM/opmask registers, MXCSR and x87
state; FS preservation is separately derived from the actual integer proof. -/
theorem preserves_extended (original : Features.State) (before final : X86.MState)
    (left right exit : Word) (ready : AdditionFunction.Ready before final left right exit) :
    (lift original final).state.zmm = original.zmm ∧
      (lift original final).state.k = original.k ∧
      (lift original final).state.mxcsr = original.mxcsr ∧
      (lift original final).state.x87 = original.x87 ∧
      (lift original final).state.core.fsBase = before.core.fsBase :=
  ⟨rfl, rfl, rfl, rfl, ready.fsBase⟩

end Silmaril.Compiler.Native.Emit.AdditionFeatures
