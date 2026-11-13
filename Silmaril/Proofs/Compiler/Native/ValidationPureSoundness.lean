module

public import Silmaril.Compiler.Native.Optimize.Validation.PureSoundness.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.PureSoundness
open Silmaril.Machine
open Silmaril.Compile
set_option maxHeartbeats 1000000

theorem accepted_block_success_with_reads (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) (values : List Lir.Word)
    (sourceRead : (Acceptance.observedRegs source).mapM sourceFrame.get = some values) :
    ∃ candidateFrame, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  obtain ⟨sameMemory, sourceMeaning, sourceResult⟩ :=
    Observation.source_block_sound calls source frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted (Acceptance.observedRegs source) values sourceRead
  change Observation.BlockResult {} (Acceptance.sourceRun source).2 sourceFrame
    (Acceptance.sourceRun source).1.1 (Acceptance.sourceRun source).1.2
    exit values (Total.initialMeaning frame) sourceMeaning at sourceResult
  obtain ⟨candidateExit, candidateFrame, candidateValues, candidateMeaning,
      candidateExecuted, candidateRead, candidateResult⟩ :=
    Candidate.seeded_block_success calls candidate candidateAdmitted (Acceptance.observedRegs source)
      frame sourceFrame memory (Acceptance.sourceRun source).2 sourceMeaning
      sourceResult.term.result sourceResult.term.total facts.partialLeaves
  change Observation.BlockResult { nodes := (Acceptance.sourceRun source).2.nodes }
    (Acceptance.candidateRun source candidate).2 candidateFrame
    (Acceptance.candidateRun source candidate).1.1 (Acceptance.candidateRun source candidate).1.2
    candidateExit candidateValues sourceMeaning candidateMeaning at candidateResult
  have sourceExit : Observation.termExit candidateMeaning (Acceptance.sourceRun source).1.1 = some exit :=
    (Observation.termExit_preserved _ candidateResult.term.result.extension
      sourceResult.term.wellScoped).trans sourceResult.term.selected
  rw [facts.term] at sourceExit
  have exitSame : candidateExit = exit := Option.some.inj (candidateResult.term.selected.symm.trans sourceExit)
  have sourceValues : (Acceptance.sourceRun source).1.2.mapM candidateMeaning.value = some values :=
    (Observation.values_preserved _ candidateResult.term.result.extension
      sourceResult.observedBounded).trans sourceResult.observed
  rw [facts.observed] at sourceValues
  have valuesSame : candidateValues = values := Option.some.inj (candidateResult.observed.symm.trans sourceValues)
  rw [sameMemory]
  exact ⟨candidateFrame, exitSame ▸ candidateExecuted, valuesSame ▸ candidateRead⟩

theorem set_preserves (frame : Lir.Frame Nat) (dest : Nat) (word : Lir.Word) :
    (frame.set dest word).slots = frame.slots ∧
      ∀ reg, reg ∉ [dest] → (frame.set dest word).get reg = frame.get reg := by
  refine ⟨rfl, ?_⟩
  intro reg outside
  have different : reg ≠ dest := by simpa only [List.mem_singleton] using outside
  simp only [Lir.Frame.get_set, ite_eq_right different]

theorem op_preserves (op : Lir.Op Nat) (frame frame' : Lir.Frame Nat)
    (memory memory' : Lir.Memory) (admitted : Roots.Admitted op)
    (executed : op.exec frame memory = some (frame', memory')) :
    frame'.slots = frame.slots ∧
      ∀ reg, reg ∉ Validation.defs (.op op) → frame'.get reg = frame.get reg := by
  cases op with
  | const dest value =>
    have result : frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.some.injEq, Prod.mk.injEq] using executed
    rw [← result.1]
    exact set_preserves frame dest value
  | move dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, _, equal, _⟩ := result
    rw [← equal]
    exact set_preserves frame dest value
  | unary op dest source =>
    have result : ∃ value, frame.get source = some value ∧
        frame.set dest (op.eval value) = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] using executed
    obtain ⟨value, _, equal, _⟩ := result
    rw [← equal]
    exact set_preserves frame dest (op.eval value)
  | binary op dest left right =>
    have result : ∃ x, frame.get left = some x ∧ ∃ y, frame.get right = some y ∧
        ∃ value, op.eval x y = some value ∧ frame.set dest value = frame' ∧ memory = memory' := by
      simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff,
        Prod.mk.injEq] using executed
    obtain ⟨_, _, _, _, value, _, equal, _⟩ := result
    rw [← equal]
    exact set_preserves frame dest value
  | load width ext dest base offset => cases admitted
  | store width base offset source => cases admitted
  | slotGet dest slot => cases admitted
  | slotSet slot source => cases admitted

theorem instruction_preserves (calls : OpenCalls) (instruction : Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Lists.AdmittedInstr instruction)
    (executed : InstructionExec calls instruction frame memory frame' memory') :
    frame'.slots = frame.slots ∧
      ∀ reg, reg ∉ Validation.defs instruction → frame'.get reg = frame.get reg := by
  cases instruction with
  | op op =>
    cases executed with
    | op actual => exact op_preserves op frame frame' memory memory' admitted actual
  | fop op dest left right => cases admitted
  | addr dest symbol offset => cases admitted
  | call symbol args results => cases admitted
  | callIndirect target args results => cases admitted

theorem instructions_preserve (calls : OpenCalls) (instructions : List Mir.Instr)
    (frame frame' : Lir.Frame Nat) (memory memory' : Lir.Memory)
    (admitted : Lists.Admitted instructions)
    (executed : InstructionsExec calls instructions frame memory frame' memory') :
    frame'.slots = frame.slots ∧
      ∀ reg, reg ∉ instructions.flatMap Validation.defs → frame'.get reg = frame.get reg := by
  induction executed with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | @cons instruction rest frame memory middle middleMemory frame' memory' first later ih =>
    have firstPreserves := instruction_preserves calls instruction frame middle memory middleMemory
      (admitted instruction (by simp)) first
    have tailPreserves := ih (fun i member => admitted i (by simp [member]))
    refine ⟨tailPreserves.1.trans firstPreserves.1, ?_⟩
    intro reg outside
    have split : reg ∉ Validation.defs instruction ∧ reg ∉ rest.flatMap Validation.defs := by
      simpa only [List.flatMap_cons, List.mem_append, not_or] using outside
    exact (tailPreserves.2 reg split.2).trans (firstPreserves.2 reg split.1)

theorem mapM_agrees {α : Type} (items : List α) (left right : α → Option Lir.Word)
    (values : List Lir.Word) (leftRead : items.mapM left = some values)
    (rightRead : items.mapM right = some values) :
    ∀ item ∈ items, left item = right item := by
  induction items generalizing values with
  | nil =>
    intro item member
    cases member
  | cons item rest ih =>
    show ∀ other ∈ item :: rest, left other = right other
    have leftParts : ∃ word, left item = some word ∧ ∃ words,
        rest.mapM left = some words ∧ word :: words = values := by
      simpa only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq] using leftRead
    have rightParts : ∃ word, right item = some word ∧ ∃ words,
        rest.mapM right = some words ∧ word :: words = values := by
      simpa only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq] using rightRead
    obtain ⟨x, hx, xs, hxs, ex⟩ := leftParts
    obtain ⟨y, hy, ys, hys, ey⟩ := rightParts
    have same : x = y ∧ xs = ys := List.cons.inj (ex.trans ey.symm)
    intro other member
    rcases List.mem_cons.mp member with equal | tail
    · simpa only [equal] using hx.trans (same.1 ▸ hy.symm)
    · exact ih xs hxs (same.2 ▸ hys) other tail

theorem accepted_block_refines_with_reads (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) (values : List Lir.Word)
    (sourceRead : (Acceptance.observedRegs source).mapM sourceFrame.get = some values) :
    ∃ candidateFrame, BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨candidateFrame, candidateExecuted, candidateRead⟩ :=
    accepted_block_success_with_reads calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted values sourceRead
  have sourcePreserves : sourceFrame.slots = frame.slots ∧
      ∀ reg, reg ∉ source.instrs.toList.flatMap Validation.defs → sourceFrame.get reg = frame.get reg :=
    instructions_preserve calls source.instrs.toList frame sourceFrame memory sourceMemory
      sourceAdmitted sourceExecuted.1
  have candidatePreserves : candidateFrame.slots = frame.slots ∧
      ∀ reg, reg ∉ candidate.instrs.toList.flatMap Validation.defs → candidateFrame.get reg = frame.get reg :=
    instructions_preserve calls candidate.instrs.toList frame candidateFrame memory sourceMemory
      candidateAdmitted candidateExecuted.1
  have facts : Acceptance.Accepted base source candidate :=
    (Acceptance.check_eq_true_iff base source candidate).mp accepted
  refine ⟨candidateFrame, candidateExecuted, candidatePreserves.1.trans sourcePreserves.1.symm, ?_, candidateRead⟩
  intro reg below
  by_cases observed : reg ∈ Acceptance.observedRegs source
  · exact (mapM_agrees _ sourceFrame.get candidateFrame.get values sourceRead candidateRead reg observed).symm
  · show candidateFrame.get reg = sourceFrame.get reg
    have sourceOutside : reg ∉ source.instrs.toList.flatMap Validation.defs := by
      simpa only [Acceptance.observedRegs, List.mem_dedup] using observed
    have candidateOutside : reg ∉ candidate.instrs.toList.flatMap Validation.defs := by
      intro written
      obtain ⟨instruction, member, defined⟩ := List.mem_flatMap.mp written
      have allowed : base ≤ reg ∨ reg ∈ Acceptance.observedRegs source :=
        Acceptance.candidate_write base source candidate facts instruction (by simpa using member) reg defined
      rcases allowed with fresh | old
      · omega
      · exact observed old
    exact (candidatePreserves.2 reg candidateOutside).trans (sourcePreserves.2 reg sourceOutside).symm

/-- Actual checker acceptance preserves every finite successful source block
execution in the admitted pure fragment. Source observations and the candidate
execution are derived; the original incoming frame may be partial. -/
theorem accepted_block_refines (calls : OpenCalls) (base : Nat)
    (source candidate : Mir.Block) (frame sourceFrame : Lir.Frame Nat)
    (memory sourceMemory : Lir.Memory) (exit : BlockExit)
    (sourceExecuted : BlockExec calls source frame memory exit sourceFrame sourceMemory)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) :
    ∃ candidateFrame values,
      BlockExec calls candidate frame memory exit candidateFrame sourceMemory ∧
      candidateFrame.slots = sourceFrame.slots ∧
      (∀ reg, reg < base → candidateFrame.get reg = sourceFrame.get reg) ∧
      (Acceptance.observedRegs source).mapM sourceFrame.get = some values ∧
      (Acceptance.observedRegs source).mapM candidateFrame.get = some values := by
  obtain ⟨values, sourceRead⟩ := SourceReads.observed_success calls source frame sourceFrame memory sourceMemory
    sourceAdmitted sourceExecuted.1
  obtain ⟨candidateFrame, candidateExecuted, slotsSame, registersSame, candidateRead⟩ :=
    accepted_block_refines_with_reads calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted values sourceRead
  exact ⟨candidateFrame, values, candidateExecuted, slotsSame, registersSame, sourceRead, candidateRead⟩

/-- Soundness of the real checker for its explicitly admitted pure fragment.
No candidate execution or successful read is a premise. -/
theorem check_sound (base : Nat) (source candidate : Mir.Block)
    (sourceAdmitted : Lists.Admitted source.instrs.toList)
    (candidateAdmitted : Lists.Admitted candidate.instrs.toList)
    (accepted : check base source candidate = true) : Preserves base source candidate := by
  intro calls frame sourceFrame memory sourceMemory exit sourceExecuted
  obtain ⟨candidateFrame, values, candidateExecuted, slotsSame, registersSame, sourceRead, candidateRead⟩ :=
    accepted_block_refines calls base source candidate frame sourceFrame memory sourceMemory exit
      sourceExecuted sourceAdmitted candidateAdmitted accepted
  exact ⟨candidateFrame, candidateExecuted, slotsSame, registersSame⟩

end Silmaril.Compiler.Native.Optimize.Validation.PureSoundness
