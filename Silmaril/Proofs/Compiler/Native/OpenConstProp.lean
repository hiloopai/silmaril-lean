module

public import Silmaril.Compiler.Native.Optimize.Open.ConstProp.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
public import Silmaril.Compiler.Native.Optimize.Validation.Machine.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.ConstProp

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

theorem instruction (summaries : OpenCalls) (facts : Facts) {instruction : Mir.Instr}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Mir.ConstProp.Holds facts source)
    (executed : InstructionExec summaries instruction source memory final finalMemory) :
    InstructionExec summaries (Mir.ConstProp.rwInstr facts instruction).1
        source memory final finalMemory ∧
      Mir.ConstProp.Holds (Mir.ConstProp.rwInstr facts instruction).2 final := by
  cases executed with
  | op executed =>
    obtain ⟨candidate, next⟩ := Mir.ConstProp.rwOp_correct held executed
    exact ⟨.op candidate, next⟩
  | @fop op dest a b source memory final executed =>
    show InstructionExec summaries (.fop op dest (Mir.ConstProp.resolve facts a)
        (Mir.ConstProp.resolve facts b)) source memory final memory ∧
      Mir.ConstProp.Holds (Mir.ConstProp.kill facts dest) final
    have rewritten : Lir.FOp.exec op dest (Mir.ConstProp.resolve facts a)
        (Mir.ConstProp.resolve facts b) source = some final := by
      simpa [Lir.FOp.exec, Mir.ConstProp.get_resolve held] using executed
    refine ⟨.fop rewritten, ?_⟩
    have values : ∃ left, source.get a = some left ∧ ∃ right, source.get b = some right ∧
        source.set dest (op.eval left right) = final := by
      simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using executed
    obtain ⟨left, _, right, _, written⟩ := values
    exact written ▸ Mir.ConstProp.holds_kill held dest (op.eval left right)
  | addr resolved => exact ⟨.addr resolved, Mir.ConstProp.holds_kill held _ _⟩
  | call read summary write =>
    refine ⟨.call ?_ summary write, Mir.ConstProp.holds_killAll held write⟩
    simpa only [Mir.ConstProp.readAll_resolve held] using read
  | indirect target read summary write =>
    refine ⟨.indirect ?_ ?_ summary write, Mir.ConstProp.holds_killAll held write⟩
    · simpa only [Mir.ConstProp.get_resolve held] using target
    · simpa only [Mir.ConstProp.readAll_resolve held] using read

theorem instructions (summaries : OpenCalls) (facts : Facts) {instructions : List Mir.Instr}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Mir.ConstProp.Holds facts source)
    (executed : InstructionsExec summaries instructions source memory final finalMemory) :
    InstructionsExec summaries (Mir.ConstProp.rwList facts instructions).1
        source memory final finalMemory ∧
      Mir.ConstProp.Holds (Mir.ConstProp.rwList facts instructions).2 final := by
  induction executed generalizing facts with
  | nil => exact ⟨.nil, held⟩
  | cons first rest ih =>
    obtain ⟨candidate, next⟩ := instruction summaries facts held first
    obtain ⟨candidateRest, last⟩ := ih _ next
    exact ⟨.cons candidate candidateRest, last⟩

theorem ret_exec_of_out {locations : List (Lir.Loc Nat)} {frame : Lir.Frame Nat} {exit : BlockExit}
    (actual : Mir.FuncPass.termOut frame (.ret locations) = Validation.Machine.termOut exit) :
    TermExec (.ret locations) frame exit := by
  cases read : frame.readAll locations with
  | none => cases exit <;> simp [Mir.FuncPass.termOut, read, Validation.Machine.termOut] at actual
  | some values =>
    cases exit <;> simp_all [Mir.FuncPass.termOut, Validation.Machine.termOut]
    exact .ret read

theorem branch_exec_of_out {reg yes no : Nat} {frame : Lir.Frame Nat} {exit : BlockExit}
    (actual : Mir.FuncPass.termOut frame (.branch reg yes no) = Validation.Machine.termOut exit) :
    TermExec (.branch reg yes no) frame exit := by
  cases read : frame.get reg with
  | none => cases exit <;> simp [Mir.FuncPass.termOut, read, Validation.Machine.termOut] at actual
  | some value =>
    by_cases zero : value = 0
    · cases exit <;> simp_all [Mir.FuncPass.termOut, Validation.Machine.termOut]
      exact .zero read
    · cases exit <;> simp_all [Mir.FuncPass.termOut, Validation.Machine.termOut]
      exact .nonzero read zero

theorem term_exec_of_out {term : Lir.Term Nat} {frame : Lir.Frame Nat} {exit : BlockExit}
    (actual : Mir.FuncPass.termOut frame term = Validation.Machine.termOut exit) :
    TermExec term frame exit := by
  cases term with
  | jump label =>
    cases exit <;> simp_all [Mir.FuncPass.termOut, Validation.Machine.termOut]
    exact .jump
  | trap =>
    cases exit <;> simp_all [Mir.FuncPass.termOut, Validation.Machine.termOut]
    exact .trap
  | ret _ => exact ret_exec_of_out actual
  | branch _ _ _ => exact branch_exec_of_out actual

theorem term (facts : Facts) {source : Lir.Frame Nat} {sourceTerm : Lir.Term Nat} {exit : BlockExit}
    (held : Mir.ConstProp.Holds facts source) (executed : TermExec sourceTerm source exit) :
    TermExec (Mir.ConstProp.rwTerm facts sourceTerm) source exit := by
  have actual := Validation.Machine.termOut_of_exec sourceTerm source exit executed
  have successful : Mir.FuncPass.termOut source sourceTerm ≠ .stuck := by
    rw [actual]
    cases exit <;> intro impossible <;> cases impossible
  exact term_exec_of_out ((Mir.ConstProp.rwTerm_correct held sourceTerm successful).trans actual)

theorem block (summaries : OpenCalls) (facts : Facts) {sourceBlock : Mir.Block}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory} {exit : BlockExit}
    (held : Mir.ConstProp.Holds facts source)
    (executed : BlockExec summaries sourceBlock source memory exit final finalMemory) :
    BlockExec summaries (Mir.ConstProp.rwBlock facts sourceBlock) source memory exit final finalMemory ∧
      Mir.ConstProp.Holds (Mir.ConstProp.fold facts sourceBlock.instrs.toList) final := by
  obtain ⟨candidate, last⟩ := instructions summaries facts held executed.1
  refine ⟨⟨?_, term _ last executed.2⟩, ?_⟩
  · simpa only [Mir.ConstProp.rwBlock, List.toList_toArray] using candidate
  · simpa only [Mir.ConstProp.rwList_snd] using last

theorem block_found {function : Mir.Func} {label : Nat} {sourceBlock : Mir.Block} {facts : Facts}
    (found : function.blocks[label]? = some sourceBlock)
    (selected : Mir.ConstProp.entryAt (Mir.ConstProp.entryFacts function) label = some facts) :
    (Mir.ConstProp.rwFunc function).blocks[label]? = some (Mir.ConstProp.rwBlock facts sourceBlock) := by
  simp only [Mir.ConstProp.rwFunc, Array.getElem?_mapIdx, found, Option.map_some, selected, Option.getD_some]

theorem entry_zero (function : Mir.Func) (frame : Lir.Frame Nat) (memory : Lir.Memory) :
    Entry function ⟨0, frame, memory⟩ := by
  refine ⟨[], (Mir.ConstProp.check_spec (Mir.ConstProp.check_entryFacts function)).1, ?_⟩
  simp [Mir.ConstProp.Holds]

theorem jump (summaries : OpenCalls) {function : Mir.Func} {source target : OpenFrame.State}
    (entry : Entry function source) (executed : OpenFrame.Step summaries function source target) :
    OpenFrame.Step summaries (Mir.ConstProp.rwFunc function) source target ∧ Entry function target := by
  obtain ⟨facts, selected, held⟩ := entry
  cases executed with
  | jump found executed =>
    obtain ⟨candidate, last⟩ := block summaries facts held executed
    have destination := Mir.ConstProp.mem_succs
      (Validation.Machine.termOut_of_exec _ _ _ executed.2)
    obtain ⟨next, nextSelected, included⟩ :=
      (Mir.ConstProp.check_spec (Mir.ConstProp.check_entryFacts function)).2 _ _ facts found selected _ destination
    refine ⟨.jump (block_found found selected) candidate, next, nextSelected, ?_⟩
    intro fact member
    exact last fact (included fact member)

theorem run (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (entry : Entry function source) (executed : OpenFrame.Run summaries function source behavior)
    (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (Mir.ConstProp.rwFunc function) source behavior := by
  revert entry successful
  induction executed with
  | @stop source behavior stopped =>
    intro entry successful
    obtain ⟨facts, selected, held⟩ := entry
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨sourceBlock, final, found, executed⟩ := stopped
      exact .stop ⟨_, final, block_found found selected, (block summaries facts held executed).1⟩
    | stuck => exact False.elim (successful rfl)
    | diverges => exact False.elim stopped
  | next step rest ih =>
    intro entry successful
    obtain ⟨candidate, nextEntry⟩ := jump summaries entry step
    exact .next candidate (ih nextEntry successful)

theorem instruction_call_free (facts : Facts) {source : Mir.Instr} (free : OpenFrame.CallFree source) :
    OpenFrame.CallFree (Mir.ConstProp.rwInstr facts source).1 := by
  cases source <;> simp_all [Mir.ConstProp.rwInstr, OpenFrame.CallFree]

theorem instructions_call_free (facts : Facts) {source : List Mir.Instr}
    (free : ∀ instruction ∈ source, OpenFrame.CallFree instruction) :
    ∀ instruction ∈ (Mir.ConstProp.rwList facts source).1, OpenFrame.CallFree instruction := by
  induction source generalizing facts with
  | nil => simp [Mir.ConstProp.rwList]
  | cons first rest ih =>
    intro instruction member
    have located : instruction = (Mir.ConstProp.rwInstr facts first).1 ∨
        instruction ∈ (Mir.ConstProp.rwList (Mir.ConstProp.rwInstr facts first).2 rest).1 := by
      simpa only [Mir.ConstProp.rwList, List.mem_cons] using member
    cases located with
    | inl same => exact same.symm ▸ instruction_call_free facts (free first (by simp))
    | inr member => exact ih _ (fun instruction member => free instruction (by simp [member])) instruction member

theorem block_call_free (facts : Facts) {source : Mir.Block} (free : OpenFrame.BlockCallFree source) :
    OpenFrame.BlockCallFree (Mir.ConstProp.rwBlock facts source) := by
  simpa only [OpenFrame.BlockCallFree, Mir.ConstProp.rwBlock, List.toList_toArray] using
    instructions_call_free facts free

theorem function_call_free {source : Mir.Func} (free : OpenFrame.FunctionCallFree source) :
    OpenFrame.FunctionCallFree (Mir.ConstProp.rwFunc source) := by
  intro label candidate found
  have selected : ∃ block, source.blocks[label]? = some block ∧
      Mir.ConstProp.rwBlock ((Mir.ConstProp.entryAt (Mir.ConstProp.entryFacts source) label).getD []) block = candidate := by
    simpa only [Mir.ConstProp.rwFunc, Array.getElem?_mapIdx, Option.map_eq_some_iff] using found
  obtain ⟨block, original, rfl⟩ := selected
  exact block_call_free _ (free label block original)

/-- A successful finite source run derives the candidate's entire observation
relation, when the independent source syntax is call-free. Candidate syntax,
execution and uniqueness are all derived; no target trace is a premise. -/
theorem observations_exact (summaries : OpenCalls) {function : Mir.Func}
    (free : OpenFrame.FunctionCallFree function) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function ⟨0, frame, memory⟩ behavior)
    (successful : behavior ≠ .stuck) (other : Lir.Behavior) :
    OpenFrame.Behaves summaries (Mir.ConstProp.rwFunc function) ⟨0, frame, memory⟩ other ↔ other = behavior := by
  have candidate : OpenFrame.Run summaries (Mir.ConstProp.rwFunc function) ⟨0, frame, memory⟩ behavior :=
    run summaries (entry_zero function frame memory) executed successful
  have candidateFree : OpenFrame.FunctionCallFree (Mir.ConstProp.rwFunc function) := function_call_free free
  constructor
  · intro observed
    cases other with
    | diverges => exact False.elim (OpenFrame.run_no_infinite candidateFree candidate observed)
    | returned values memory | trapped memory | stuck =>
      obtain ⟨final, steps, stopped⟩ := observed
      exact (OpenFrame.run_unique candidateFree candidate (OpenFrame.run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact OpenFrame.run_behaves candidate

end Silmaril.Compiler.Native.Optimize.Open.ConstProp
