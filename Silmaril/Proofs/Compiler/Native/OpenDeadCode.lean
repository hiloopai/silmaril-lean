module

public import Silmaril.Compiler.Native.Optimize.Open.DeadCode.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.DeadCode
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

theorem writeAll_exists {source final : Lir.Frame Nat} {registers : List Nat} {words : List Lir.Word}
    (written : source.writeAll (registers.map .reg) words = some final) (candidate : Lir.Frame Nat) :
    ∃ candidateFinal, candidate.writeAll (registers.map .reg) words = some candidateFinal := by
  induction registers generalizing source candidate words with
  | nil =>
    cases words with
    | nil => exact ⟨candidate, rfl⟩
    | cons _ _ => cases written
  | cons reg rest ih =>
    cases words with
    | nil => cases written
    | cons word words => exact ih written (candidate.set reg word)

/-- A retained instruction reuses actual operands, open effects and result
writes; candidate execution is derived from actual source execution. -/
theorem instruction (summaries : OpenCalls) (live : LiveSet) {instruction : Mir.Instr}
    {source candidate final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Agree (Mir.DeadCode.instrLive live instruction) source candidate)
    (executed : InstructionExec summaries instruction source memory final finalMemory) :
    ∃ candidateFinal, InstructionExec summaries instruction candidate memory candidateFinal finalMemory ∧
      Agree live final candidateFinal := by
  cases executed with
  | op actual =>
    obtain ⟨candidateFinal, candidateExecuted, agreed⟩ := Mir.DeadCode.op_agree held actual
    exact ⟨candidateFinal, .op candidateExecuted, agreed⟩
  | @fop operation dest left right source memory final actual =>
    show ∃ candidateFinal, InstructionExec summaries (.fop operation dest left right) candidate memory candidateFinal memory ∧
      Agree live final candidateFinal
    have values : ∃ x, source.get left = some x ∧ ∃ y, source.get right = some y ∧
        source.set dest (operation.eval x y) = final := by
      simpa only [Lir.FOp.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] using actual
    obtain ⟨x, readLeft, y, readRight, written⟩ := values
    have leftSame : candidate.get left = source.get left := held.2 left (by
      simp [Mir.DeadCode.instrLive, Mir.DeadCode.RSet.mem_insert])
    have rightSame : candidate.get right = source.get right := held.2 right (by
      simp [Mir.DeadCode.instrLive, Mir.DeadCode.RSet.mem_insert])
    have before : Agree (live.erase dest) source candidate := held.mono fun reg member => by
      simp [Mir.DeadCode.instrLive, Mir.DeadCode.RSet.mem_insert, member]
    refine ⟨candidate.set dest (operation.eval x y), .fop ?_, ?_⟩
    · simp only [Lir.FOp.exec, leftSame, rightSame, readLeft, readRight, Option.bind_some, Option.map_some]
    · exact written ▸ before.set (operation.eval x y)
  | addr resolved => exact ⟨_, .addr resolved, held.set _⟩
  | call read summary written =>
    obtain ⟨candidateFinal, candidateWritten⟩ := writeAll_exists written candidate
    exact ⟨candidateFinal, .call (by rw [Mir.DeadCode.readAll_regs_agree held, read]) summary candidateWritten,
      held.base.writeAll written candidateWritten⟩
  | @indirect reg args results source memory pointer values returned final finalMemory target read summary written =>
    show ∃ candidateFinal, InstructionExec summaries (.callIndirect reg args results) candidate memory candidateFinal finalMemory ∧
      Agree live final candidateFinal
    have targetSame : candidate.get reg = source.get reg := held.2 reg (by
      simp [Mir.DeadCode.instrLive, Mir.DeadCode.RSet.mem_insert])
    have arguments : Agree ((live.eraseAll results).addAll args) source candidate := held.mono fun other member => by
      simp [Mir.DeadCode.instrLive, Mir.DeadCode.RSet.mem_insert, member]
    obtain ⟨candidateFinal, candidateWritten⟩ := writeAll_exists written candidate
    exact ⟨candidateFinal, .indirect (targetSame.trans target)
      (by rw [Mir.DeadCode.readAll_regs_agree arguments, read]) summary candidateWritten,
      arguments.base.writeAll written candidateWritten⟩

theorem instructions (summaries : OpenCalls) (live : LiveSet) {instructions : List Mir.Instr}
    {source candidate final : Lir.Frame Nat} {memory finalMemory : Lir.Memory}
    (held : Agree (Mir.DeadCode.dceList live instructions).2 source candidate)
    (executed : InstructionsExec summaries instructions source memory final finalMemory) :
    ∃ candidateFinal,
      InstructionsExec summaries (Mir.DeadCode.dceList live instructions).1 candidate memory candidateFinal finalMemory ∧
      Agree live final candidateFinal := by
  induction executed generalizing live candidate with
  | nil => exact ⟨candidate, .nil, held⟩
  | @cons first rest source memory middle middleMemory final finalMemory firstExecuted restExecuted ih =>
    show ∃ candidateFinal,
      InstructionsExec summaries (Mir.DeadCode.dceList live (first :: rest)).1 candidate memory candidateFinal finalMemory ∧
      Agree live final candidateFinal
    cases removed : Mir.DeadCode.dead (Mir.DeadCode.dceList live rest).2 first with
    | false =>
      have before : Agree (Mir.DeadCode.instrLive (Mir.DeadCode.dceList live rest).2 first) source candidate := by
        simpa only [Mir.DeadCode.dceList, removed, Bool.false_eq_true, ↓reduceIte] using held
      obtain ⟨candidateMiddle, firstCandidate, next⟩ := instruction summaries _ before firstExecuted
      obtain ⟨candidateFinal, restCandidate, agreed⟩ := ih live next
      exact ⟨candidateFinal, by
        simpa only [Mir.DeadCode.dceList, removed, Bool.false_eq_true, ↓reduceIte] using
          InstructionsExec.cons firstCandidate restCandidate, agreed⟩
    | true =>
      show ∃ candidateFinal,
        InstructionsExec summaries (Mir.DeadCode.dceList live (first :: rest)).1 candidate memory candidateFinal finalMemory ∧
        Agree live final candidateFinal
      have before : Agree (Mir.DeadCode.dceList live rest).2 source candidate := by
        simpa only [Mir.DeadCode.dceList, removed, ↓reduceIte] using held
      cases firstExecuted with
      | op actual =>
        obtain ⟨rfl, next⟩ := Mir.DeadCode.dead_exec removed before actual
        obtain ⟨candidateFinal, restCandidate, agreed⟩ := ih live next
        exact ⟨candidateFinal, by simpa only [Mir.DeadCode.dceList, removed, ↓reduceIte] using restCandidate, agreed⟩
      | fop _ | addr _ | call _ _ _ | indirect _ _ _ _ => simp [Mir.DeadCode.dead] at removed

theorem term (certificate : Array LiveSet) {source candidate : Lir.Frame Nat} {term : Lir.Term Nat} {exit : BlockExit}
    (held : Agree ((Mir.DeadCode.liveOut certificate term).addAll (Mir.DeadCode.termUses term)) source candidate)
    (executed : TermExec term source exit) : TermExec term candidate exit := by
  cases executed with
  | jump => exact .jump
  | zero read =>
    exact .zero ((held.get (by simp [Mir.DeadCode.termUses])).trans read)
  | nonzero read nonzero =>
    exact .nonzero ((held.get (by simp [Mir.DeadCode.termUses])).trans read) nonzero
  | ret read =>
    apply TermExec.ret
    rw [Mir.DeadCode.readAll_agree held.1 (fun reg member => held.get (by
      simp only [Mir.DeadCode.termUses, List.mem_filterMap]
      exact ⟨.reg reg, member, rfl⟩))]
    exact read
  | trap => exact .trap

theorem successor (certificate : Array LiveSet) {source candidate : Lir.Frame Nat}
    {term : Lir.Term Nat} {label : Nat}
    (held : Agree ((Mir.DeadCode.liveOut certificate term).addAll (Mir.DeadCode.termUses term)) source candidate)
    (executed : TermExec term source (.jump label)) : Agree (certificate.getD label 0) source candidate := by
  cases executed with
  | jump => exact held.base
  | zero _ =>
    apply held.base.mono
    intro reg member
    simp only [Mir.DeadCode.liveOut, Nat.testBit_or, Bool.or_eq_true]
    exact Or.inr member
  | nonzero _ _ =>
    apply held.base.mono
    intro reg member
    simp only [Mir.DeadCode.liveOut, Nat.testBit_or, Bool.or_eq_true]
    exact Or.inl member

theorem block (summaries : OpenCalls) (certificate : Array LiveSet) {sourceBlock : Mir.Block}
    {source candidate final : Lir.Frame Nat} {memory finalMemory : Lir.Memory} {exit : BlockExit}
    (held : Agree (Mir.DeadCode.blockLive certificate sourceBlock).2 source candidate)
    (executed : BlockExec summaries sourceBlock source memory exit final finalMemory) :
    ∃ candidateFinal, BlockExec summaries (Mir.DeadCode.dceBlock certificate sourceBlock)
      candidate memory exit candidateFinal finalMemory ∧
      Agree (Mir.DeadCode.liveEnd certificate sourceBlock) final candidateFinal := by
  obtain ⟨candidateFinal, actual, agreed⟩ := instructions summaries _ held executed.1
  refine ⟨candidateFinal, ⟨?_, term certificate agreed executed.2⟩, agreed⟩
  simpa only [Mir.DeadCode.dceBlock, Mir.DeadCode.blockLive, List.toList_toArray] using actual

theorem block_found (certificate : Array LiveSet) {function : Mir.Func} {label : Nat} {sourceBlock : Mir.Block}
    (found : function.blocks[label]? = some sourceBlock) :
    (checkedFunction certificate function).blocks[label]? = some (Mir.DeadCode.dceBlock certificate sourceBlock) := by
  simp only [checkedFunction, Array.getElem?_map, found, Option.map_some]

theorem entry (certificate : Array LiveSet) {function : Mir.Func} {label : Nat} {sourceBlock : Mir.Block}
    (checked : Mir.DeadCode.check certificate function = true) (found : function.blocks[label]? = some sourceBlock)
    {source candidate : Lir.Frame Nat} (held : Agree (certificate.getD label 0) source candidate) :
    Agree (Mir.DeadCode.blockLive certificate sourceBlock).2 source candidate :=
  held.mono fun _ member => Mir.DeadCode.RSet.mem_of_subset (Mir.DeadCode.check_spec checked found) member

theorem checked_run (summaries : OpenCalls) (certificate : Array LiveSet) {function : Mir.Func}
    (checked : Mir.DeadCode.check certificate function = true)
    {source : OpenFrame.State} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck)
    (candidate : Lir.Frame Nat) (held : Agree (certificate.getD source.label 0) source.frame candidate) :
    OpenFrame.Run summaries (checkedFunction certificate function) ⟨source.label, candidate, source.memory⟩ behavior := by
  revert candidate held successful
  induction executed with
  | @stop source behavior stopped =>
    intro successful candidate held
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨sourceBlock, final, found, actual⟩ := stopped
      obtain ⟨candidateFinal, candidateExecuted, _⟩ := block summaries certificate (entry certificate checked found held) actual
      exact .stop ⟨_, candidateFinal, block_found certificate found, candidateExecuted⟩
    | stuck => exact False.elim (successful rfl)
    | diverges => exact False.elim stopped
  | next step rest ih =>
    intro successful candidate held
    cases step with
    | jump found actual =>
      obtain ⟨candidateFinal, candidateExecuted, agreed⟩ := block summaries certificate (entry certificate checked found held) actual
      exact .next (.jump (block_found certificate found) candidateExecuted)
        (ih successful candidateFinal (successor certificate agreed actual.2))

theorem run (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (Mir.DeadCode.dceFunc function) source behavior := by
  by_cases checked : Mir.DeadCode.check (Mir.DeadCode.certOf function) function = true
  · have actual := checked_run summaries (Mir.DeadCode.certOf function) checked executed successful source.frame
      ⟨rfl, fun _ _ => rfl⟩
    simpa only [Mir.DeadCode.dceFunc, checked, ↓reduceIte, checkedFunction] using actual
  · simpa only [Mir.DeadCode.dceFunc, checked, Bool.false_eq_true, ↓reduceIte] using executed

theorem instructions_call_free (live : LiveSet) {source : List Mir.Instr}
    (free : ∀ instruction ∈ source, OpenFrame.CallFree instruction) :
    ∀ instruction ∈ (Mir.DeadCode.dceList live source).1, OpenFrame.CallFree instruction := by
  induction source with
  | nil => simp [Mir.DeadCode.dceList]
  | cons first rest ih =>
    have tailFree : ∀ instruction ∈ (Mir.DeadCode.dceList live rest).1, OpenFrame.CallFree instruction :=
      ih (fun instruction member => free instruction (by simp [member]))
    cases removed : Mir.DeadCode.dead (Mir.DeadCode.dceList live rest).2 first with
    | true => simpa only [Mir.DeadCode.dceList, removed, ↓reduceIte] using tailFree
    | false =>
      intro instruction member
      have located : instruction = first ∨ instruction ∈ (Mir.DeadCode.dceList live rest).1 := by
        simpa only [Mir.DeadCode.dceList, removed, Bool.false_eq_true, ↓reduceIte, List.mem_cons] using member
      rcases located with same | later
      · exact same.symm ▸ free first (by simp)
      · exact tailFree instruction later

theorem block_call_free (certificate : Array LiveSet) {source : Mir.Block} (free : OpenFrame.BlockCallFree source) :
    OpenFrame.BlockCallFree (Mir.DeadCode.dceBlock certificate source) := by
  simpa only [OpenFrame.BlockCallFree, Mir.DeadCode.dceBlock, Mir.DeadCode.blockLive, List.toList_toArray] using
    instructions_call_free (Mir.DeadCode.liveEnd certificate source) free

theorem checked_function_call_free (certificate : Array LiveSet) {source : Mir.Func}
    (free : OpenFrame.FunctionCallFree source) : OpenFrame.FunctionCallFree (checkedFunction certificate source) := by
  intro label candidate found
  have selected : ∃ block, source.blocks[label]? = some block ∧ Mir.DeadCode.dceBlock certificate block = candidate := by
    simpa only [checkedFunction, Array.getElem?_map, Option.map_eq_some_iff] using found
  obtain ⟨block, original, rfl⟩ := selected
  exact block_call_free certificate (free label block original)

theorem function_call_free {source : Mir.Func} (free : OpenFrame.FunctionCallFree source) :
    OpenFrame.FunctionCallFree (Mir.DeadCode.dceFunc source) := by
  by_cases checked : Mir.DeadCode.check (Mir.DeadCode.certOf source) source = true
  · simpa only [Mir.DeadCode.dceFunc, checked, ↓reduceIte, checkedFunction] using
      checked_function_call_free (Mir.DeadCode.certOf source) free
  · simpa only [Mir.DeadCode.dceFunc, checked, Bool.false_eq_true, ↓reduceIte] using free

theorem observations_exact (summaries : OpenCalls) {function : Mir.Func}
    (free : OpenFrame.FunctionCallFree function) (source : OpenFrame.State) {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck)
    (other : Lir.Behavior) :
    OpenFrame.Behaves summaries (Mir.DeadCode.dceFunc function) source other ↔ other = behavior := by
  have candidate : OpenFrame.Run summaries (Mir.DeadCode.dceFunc function) source behavior := run summaries executed successful
  have candidateFree : OpenFrame.FunctionCallFree (Mir.DeadCode.dceFunc function) := function_call_free free
  constructor
  · intro observed
    cases other with
    | diverges => exact False.elim (OpenFrame.run_no_infinite candidateFree candidate observed)
    | returned values memory | trapped memory | stuck =>
      obtain ⟨final, steps, stopped⟩ := observed
      exact (OpenFrame.run_unique candidateFree candidate (OpenFrame.run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact OpenFrame.run_behaves candidate

end Silmaril.Compiler.Native.Optimize.Open.DeadCode
