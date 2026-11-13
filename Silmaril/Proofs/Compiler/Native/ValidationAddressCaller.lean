module

public import Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Caller.Defs
@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Caller
open Silmaril.Machine Silmaril.Compile Silmaril.Compile.Contract
open PureSoundness

theorem pure_admitted (instructions : List Mir.Instr) (admitted : Lists.Admitted instructions) : Admitted instructions := by
  intro instruction member
  have atInstruction : Lists.AdmittedInstr instruction := admitted instruction member
  cases instruction with
  | op operation => trivial
  | fop | addr | call | callIndirect => cases atInstruction

theorem admitted_cons (head : Mir.Instr) (tail : List Mir.Instr) :
    Admitted (head :: tail) ↔ AdmittedInstr head ∧ Admitted tail := by
  simp [Admitted]

theorem renameInstr_admitted_iff (state : Rename) (instruction : Mir.Instr) :
    AdmittedInstr ((renameInstr instruction).run state).1 ↔
      AdmittedInstr instruction := by
  cases instruction <;> rfl

theorem renameList_admitted_iff (state : Rename) (instructions : List Mir.Instr) :
    Admitted ((instructions.mapM renameInstr).run state).1 ↔
      Admitted instructions := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [renameInstrs_cons]
    change Admitted (((renameInstr instruction).run state).1 ::
      ((rest.mapM renameInstr).run ((renameInstr instruction).run state).2).1) ↔
        Admitted (instruction :: rest)
    rw [admitted_cons, admitted_cons, renameInstr_admitted_iff, ih]

theorem enter_admitted_iff (base : Nat) (source : Mir.Block) :
    Admitted (enter base source).body.instrs.toList ↔
      Admitted source.instrs.toList := by
  simpa only [enter, renameArray_run, List.toList_toArray] using
    renameList_admitted_iff ({next := base} : Rename) source.instrs.toList


theorem leave_enter_admitted (base : Nat) (source : Mir.Block)
    (admitted : Admitted source.instrs.toList) :
    Admitted (leave (enter base source)).instrs.toList := by
  have renamed : Admitted (enter base source).body.instrs.toList :=
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
theorem fallback_preserves (units : Array Mir.Unit) (placement : MirSem.Placement) (base : Nat) (source : Mir.Block)
    (admitted : Admitted source.instrs.toList) :
    Soundness.Preserves units placement base source (if (enter base source).isSSA && Validation.check base source (leave (enter base source))
      then leave (enter base source) else source) := by
  by_cases accepted : ((enter base source).isSSA && Validation.check base source (leave (enter base source))) = true
  · simp only [accepted, ↓reduceIte]
    have both : (enter base source).isSSA = true ∧ Validation.check base source (leave (enter base source)) = true := by
      simpa only [Bool.and_eq_true] using accepted
    exact Soundness.check_sound units placement base source (leave (enter base source)) admitted (leave_enter_admitted base source admitted) both.2
  · simp only [accepted]
    intro frame final memory after exit executed
    exact ⟨final, executed, Validation.Context.agrees_refl base final⟩


theorem roundTripBlock_admitted (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Admitted source.instrs.toList) :
    Admitted (roundTripBlock cfg base source).instrs.toList := by
  have fallback : Admitted
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

theorem roundTripBlock_preserves (units : Array Mir.Unit) (placement : MirSem.Placement) (cfg : Config) (base : Nat) (source : Mir.Block)
    (admitted : Admitted source.instrs.toList) :
    Soundness.Preserves units placement base source (roundTripBlock cfg base source) := by
  cases enabled : cfg.lambdaSSA with
  | false =>
    simpa only [roundTripBlock, enabled, Bool.false_eq_true, ↓reduceIte] using fallback_preserves units placement base source admitted
  | true =>
    show Soundness.Preserves units placement base source (roundTripBlock cfg base source)
    cases selected : LambdaSSA.optimize? base source with
    | none =>
      simpa only [roundTripBlock, enabled, ↓reduceIte, selected, Option.map_none, Option.getD_none] using
        fallback_preserves units placement base source admitted
    | some result =>
      obtain ⟨candidate, count⟩ := result
      rw [LambdaSSA.SelectedSoundness.roundTripBlock_selected cfg base source candidate count enabled selected]
      intro frame final memory after exit executed
      exact LambdaSSA.SelectedSoundness.optimize_preserves selected (calls units placement) frame final memory after exit executed

/-- The real selected caller starts from its own related partial input.
Successful source execution alone yields actual target execution and full
low/slot agreement; actual function membership supplies the read bounds. -/
theorem roundTripBlock_contextual (units : Array Mir.Unit) (placement : MirSem.Placement)
    {function : Mir.Func} {source : Mir.Block} (member : source ∈ function.blocks.toList)
    (admitted : Admitted source.instrs.toList) (cfg : Config)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidateFinal values,
      BlockExec (calls units placement) (roundTripBlock cfg (freshBase function) source)
        candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal ∧
      (Acceptance.observedRegs source).mapM sourceFinal.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFinal.get = some values := by
  obtain ⟨transportedFinal, transportedRun, transportedAgree⟩ := Context.block_transport
    (calls units placement) (freshBase function) source admitted (Validation.Context.freshBase_reads member)
      sourceInput candidateInput sourceFinal agrees memory finalMemory exit executed
  obtain ⟨candidateFinal, candidateRun, candidateAgree⟩ := roundTripBlock_preserves units placement
    cfg (freshBase function) source admitted candidateInput transportedFinal memory finalMemory exit transportedRun
  have finalAgree := Validation.Context.agrees_trans transportedAgree candidateAgree
  obtain ⟨values, sourceRead, candidateRead⟩ := Context.function_output_reads units placement member admitted
    sourceInput sourceFinal candidateFinal memory finalMemory exit executed finalAgree
  exact ⟨candidateFinal, values, candidateRun, finalAgree, sourceRead, candidateRead⟩

/-- Actual indexed source lookup determines the exact real versionFunc block.
No manually supplied candidate or execution/invariant of it is a premise. -/
theorem versionFunc_block_contextual (units : Array Mir.Unit) (placement : MirSem.Placement)
    {function : Mir.Func} {source : Mir.Block} {index : Nat}
    (found : function.blocks[index]? = some source)
    (admitted : Admitted source.instrs.toList) (cfg : Config)
    (sourceInput candidateInput sourceFinal : Lir.Frame Nat)
    (agrees : FrameAgrees (freshBase function) sourceInput candidateInput)
    (memory finalMemory : Lir.Memory) (exit : BlockExit)
    (executed : BlockExec (calls units placement) source sourceInput memory exit sourceFinal finalMemory) :
    ∃ candidate candidateFinal values,
      (versionFunc cfg function).blocks[index]? = some candidate ∧
      BlockExec (calls units placement) candidate candidateInput memory exit candidateFinal finalMemory ∧
      FrameAgrees (freshBase function) sourceFinal candidateFinal ∧
      (Acceptance.observedRegs source).mapM sourceFinal.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFinal.get = some values := by
  have member : source ∈ function.blocks.toList := List.mem_of_getElem? (by
    simpa only [Array.getElem?_toList] using found)
  obtain ⟨candidateFinal, values, candidateRun, candidateAgree, sourceRead, candidateRead⟩ :=
    roundTripBlock_contextual units placement member admitted cfg sourceInput candidateInput sourceFinal
      agrees memory finalMemory exit executed
  exact ⟨roundTripBlock cfg (freshBase function) source, candidateFinal, values,
    LambdaSSA.ContextualSoundness.versionFunc_block found cfg, candidateRun, candidateAgree, sourceRead, candidateRead⟩

theorem versionFunc_admitted (cfg : Config) {function : Mir.Func}
    (admitted : ∀ source ∈ function.blocks.toList, Admitted source.instrs.toList) :
    ∀ candidate ∈ (versionFunc cfg function).blocks.toList, Admitted candidate.instrs.toList := by
  intro candidate member
  change candidate ∈ (function.blocks.map (roundTripBlock cfg (freshBase function))).toList at member
  rw [Array.toList_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
  exact roundTripBlock_admitted cfg (freshBase function) source (admitted source sourceMember)

end Silmaril.Compiler.Native.Optimize.Validation.Address.Effects.Caller
