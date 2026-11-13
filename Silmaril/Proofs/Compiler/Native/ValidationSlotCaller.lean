module

public import Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller.Defs
@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller
open Silmaril.Machine Silmaril.Compile
open PureSoundness

theorem pure_op_admitted (operation : Lir.Op Nat) (admitted : Roots.Admitted operation) : Slots.AdmittedOp operation := by
  cases operation <;> simp_all only [Slots.AdmittedOp, Roots.Admitted]

theorem pure_admitted (instructions : List Mir.Instr) (admitted : Lists.Admitted instructions) : Slots.Admitted instructions := by
  intro instruction member
  have atInstruction := admitted instruction member
  cases instruction with
  | op operation => exact pure_op_admitted operation atInstruction
  | fop | addr | call | callIndirect => cases atInstruction

theorem admitted_cons (head : Mir.Instr) (tail : List Mir.Instr) :
    Slots.Admitted (head :: tail) ↔ Slots.AdmittedInstr head ∧ Slots.Admitted tail := by
  simp [Slots.Admitted]

theorem renameOp_admitted_iff (state : Rename) (operation : Lir.Op Nat) :
    Slots.AdmittedOp ((renameOp operation).run state).1 ↔ Slots.AdmittedOp operation := by
  cases operation <;> rfl

theorem renameInstr_admitted_iff (state : Rename) (instruction : Mir.Instr) :
    Slots.AdmittedInstr ((renameInstr instruction).run state).1 ↔
      Slots.AdmittedInstr instruction := by
  cases instruction with
  | op operation => exact renameOp_admitted_iff state operation
  | fop | addr | call | callIndirect => rfl

theorem renameList_admitted_iff (state : Rename) (instructions : List Mir.Instr) :
    Slots.Admitted ((instructions.mapM renameInstr).run state).1 ↔
      Slots.Admitted instructions := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [renameInstrs_cons]
    change Slots.Admitted (((renameInstr instruction).run state).1 ::
      ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).1) ↔
        Slots.Admitted (instruction :: rest)
    rw [admitted_cons, admitted_cons, renameInstr_admitted_iff, ih]

theorem enter_admitted_iff (base : Nat) (source : Mir.Block) :
    Slots.Admitted (enter base source).body.instrs.toList ↔
      Slots.Admitted source.instrs.toList := by
  simpa only [enter, renameArray_run, List.toList_toArray] using
    renameList_admitted_iff ({next := base} : Rename) source.instrs.toList


theorem leave_enter_admitted (base : Nat) (source : Mir.Block)
    (admitted : Slots.Admitted source.instrs.toList) :
    Slots.Admitted (leave (enter base source)).instrs.toList := by
  have renamed : Slots.Admitted (enter base source).body.instrs.toList :=
    (enter_admitted_iff base source).mpr admitted
  intro instruction member
  change instruction ∈ ((enter base source).body.instrs ++
    (enter base source).outputs.toArray.map (fun (original, version) => Mir.Instr.op (.move original version))).toList at member
  rw [Array.toList_append] at member
  rcases List.mem_append.mp member with original | commit
  · exact renamed instruction original
  · obtain ⟨pair, _, same⟩ := List.mem_map.mp (by simpa only [Array.toList_map, List.toList_toArray] using commit)
    subst instruction
    trivial

/-- The exact existing fallback either passes its actual retained checker or
returns the original source. The extra isSSA test is retained verbatim. -/
theorem fallback_preserves (base : Nat) (source : Mir.Block)
    (admitted : Slots.Admitted source.instrs.toList) :
    Preserves base source (if (enter base source).isSSA && Validation.check base source (leave (enter base source))
      then leave (enter base source) else source) := by
  by_cases accepted : ((enter base source).isSSA && Validation.check base source (leave (enter base source))) = true
  · simp only [accepted, ↓reduceIte]
    have both : (enter base source).isSSA = true ∧ Validation.check base source (leave (enter base source)) = true := by
      simpa only [Bool.and_eq_true] using accepted
    exact Slots.Soundness.check_sound base source (leave (enter base source)) admitted (leave_enter_admitted base source admitted) both.2
  · simp only [accepted]
    exact LambdaSSA.SelectedSoundness.preserves_refl base source


theorem roundTripBlock_admitted (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Slots.Admitted source.instrs.toList) :
    Slots.Admitted (roundTripBlock cfg base source).instrs.toList := by
  have fallback : Slots.Admitted
      (if (enter base source).isSSA && check base source (leave (enter base source))
        then leave (enter base source) else source).instrs.toList := by
    split
    · exact leave_enter_admitted base source admitted
    · exact admitted
  cases enabled : cfg.lambdaSSA with
  | false => simpa only [roundTripBlock, enabled, Bool.false_eq_true, ↓reduceIte] using fallback
  | true =>
    cases selected : LambdaSSA.optimize? base source with
    | none => simpa only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_none, Option.getD_none] using fallback
    | some result =>
      obtain ⟨candidate, count⟩ := result
      rw [LambdaSSA.SelectedSoundness.roundTripBlock_selected cfg base source candidate count enabled selected]
      exact pure_admitted _ (LambdaSSA.OptimizerAdmission.optimize_admitted selected).2.1

theorem roundTripBlock_preserves (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Slots.Admitted source.instrs.toList) :
    Preserves base source (roundTripBlock cfg base source) := by
  cases enabled : cfg.lambdaSSA with
  | false =>
    simpa only [roundTripBlock, enabled, Bool.false_eq_true, ↓reduceIte] using fallback_preserves base source admitted
  | true =>
    show Preserves base source (roundTripBlock cfg base source)
    cases selected : LambdaSSA.optimize? base source with
    | none =>
      simpa only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_none, Option.getD_none] using
        fallback_preserves base source admitted
    | some result =>
      obtain ⟨candidate, count⟩ := result
      rw [LambdaSSA.SelectedSoundness.roundTripBlock_selected cfg base source candidate count enabled selected]
      exact LambdaSSA.SelectedSoundness.optimize_preserves selected

theorem roundTripBlock_contextual {function : Mir.Func} {source : Mir.Block}
    (member : source ∈ function.blocks.toList)
    (admitted : Slots.Admitted source.instrs.toList) (cfg : Config)
    (calls : OpenCalls) (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec calls source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal, BlockExec calls (roundTripBlock cfg (freshBase function) source)
        candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := Slots.Context.block_transport
    calls (freshBase function) source admitted (Validation.Context.freshBase_reads member)
      sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := roundTripBlock_preserves
    cfg (freshBase function) source admitted calls candidateInput transportedFinal memory finalMemory exit transportedRun
  exact ⟨candidateFinal, candidateRun, Validation.Context.agrees_trans transportedAgree candidateAgree⟩


theorem versionFunc_block_contextual {function : Mir.Func} {source : Mir.Block} {index : Nat}
    (found : function.blocks[index]? = some source)
    (admitted : Slots.Admitted source.instrs.toList) (cfg : Config)
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
  exact ⟨roundTripBlock cfg (freshBase function) source, candidateFinal, LambdaSSA.ContextualSoundness.versionFunc_block found cfg,
    candidateRun, candidateAgree⟩

theorem versionFunc_admitted (cfg : Config) {function : Mir.Func}
    (admitted : ∀ source ∈ function.blocks.toList, Slots.Admitted source.instrs.toList) :
    ∀ candidate ∈ (versionFunc cfg function).blocks.toList, Slots.Admitted candidate.instrs.toList := by
  intro candidate member
  change candidate ∈ (function.blocks.map (roundTripBlock cfg (freshBase function))).toList at member
  rw [Array.toList_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact roundTripBlock_admitted cfg (freshBase function) source (admitted source sourceMember)

end Silmaril.Compiler.Native.Optimize.Validation.Slots.Caller
