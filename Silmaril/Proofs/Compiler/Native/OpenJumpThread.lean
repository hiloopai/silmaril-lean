module

public import Silmaril.Compiler.Native.Optimize.Open.JumpThread.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Open.JumpThread

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics

theorem term (function : Mir.Func) {source : Lir.Frame Nat} {sourceTerm : Lir.Term Nat} {exit : BlockExit}
    (executed : TermExec sourceTerm source exit) :
    TermExec (Mir.JumpThread.threadTerm function sourceTerm) source (threadedExit function exit) := by
  cases executed with
  | jump => exact .jump
  | zero read => exact .zero read
  | nonzero read nonzero => exact .nonzero read nonzero
  | ret read => exact .ret read
  | trap => exact .trap

theorem block (summaries : OpenCalls) (function : Mir.Func) {sourceBlock : Mir.Block}
    {source final : Lir.Frame Nat} {memory finalMemory : Lir.Memory} {exit : BlockExit}
    (executed : BlockExec summaries sourceBlock source memory exit final finalMemory) :
    BlockExec summaries (threadedBlock function sourceBlock) source memory (threadedExit function exit) final finalMemory :=
  ⟨executed.1, term function executed.2⟩

theorem block_found {function : Mir.Func} {label : Nat} {sourceBlock : Mir.Block}
    (found : function.blocks[label]? = some sourceBlock) :
    (Mir.JumpThread.jtFunc function).blocks[label]? = some (threadedBlock function sourceBlock) := by
  simp only [Mir.JumpThread.blocks_get, found, Option.map_some, threadedBlock]

theorem jump (summaries : OpenCalls) {function : Mir.Func} {source target : OpenFrame.State}
    (executed : OpenFrame.Step summaries function source target) :
    OpenFrame.Step summaries (Mir.JumpThread.jtFunc function) source
      ⟨Mir.JumpThread.dest function target.label, target.frame, target.memory⟩ := by
  cases executed with
  | jump found actual => exact .jump (block_found found) (block summaries function actual)

/-- A successful `next` is exactly an actual empty jumping block. -/
theorem next_spec {function : Mir.Func} {label target : Nat}
    (selected : Mir.JumpThread.next function label = some target) :
    function.blocks[label]? = some ⟨#[], .jump target⟩ := by
  unfold Mir.JumpThread.next at selected
  cases found : function.blocks[label]? with
  | none =>
    simp only [found] at selected
    cases selected
  | some sourceBlock =>
    simp only [found] at selected
    split at selected
    · rename_i empty
      have emptyInstructions : sourceBlock.instrs = #[] := Array.eq_empty_of_size_eq_zero empty
      cases sourceBlock with
      | mk instructions terminator =>
        simp only at emptyInstructions
        subst instructions
        cases terminator <;> simp_all
    · cases selected

/-- Empty jumps cannot change frame or memory or select a different successor. -/
theorem next_step (summaries : OpenCalls) {function : Mir.Func} {source target : OpenFrame.State} {label : Nat}
    (selected : Mir.JumpThread.next function source.label = some label)
    (executed : OpenFrame.Step summaries function source target) :
    target = ⟨label, source.frame, source.memory⟩ := by
  have found := next_spec selected
  cases executed with
  | jump otherFound actual =>
    have same := Option.some.inj (found.symm.trans otherFound)
    subst same
    have empty : BlockExec summaries (⟨#[], .jump label⟩ : Mir.Block)
        source.frame source.memory (.jump label) source.frame source.memory := ⟨.nil, .jump⟩
    obtain ⟨exit, rfl, rfl⟩ := OpenFrame.block_unique (by simp [OpenFrame.BlockCallFree]) actual empty
    cases exit
    rfl

/-- A successfully terminating block is never an empty jump. -/
theorem next_none_of_stops (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State}
    {behavior : Lir.Behavior} (stopped : OpenFrame.Stops summaries function source behavior)
    (successful : behavior ≠ .stuck) : Mir.JumpThread.next function source.label = none := by
  cases selected : Mir.JumpThread.next function source.label with
  | none => rfl
  | some label =>
    have found := next_spec selected
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨sourceBlock, final, otherFound, actual⟩ := stopped
      have same := Option.some.inj (found.symm.trans otherFound)
      subst same
      have empty : BlockExec summaries (⟨#[], .jump label⟩ : Mir.Block)
          source.frame source.memory (.jump label) source.frame source.memory := ⟨.nil, .jump⟩
      have exit := (OpenFrame.block_unique (by simp [OpenFrame.BlockCallFree]) actual empty).1
      cases exit
    | stuck => exact False.elim (successful rfl)
    | diverges => exact False.elim stopped

theorem thread_fixed {function : Mir.Func} {label : Nat}
    (terminal : Mir.JumpThread.next function label = none) (fuel : Nat) :
    Mir.JumpThread.thread function fuel label = label := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [Mir.JumpThread.thread, terminal]

/-- Strengthen over every actual thread fuel, so source empty jumps may be
skipped directly by the source-run induction, including bounded cyclic syntax. -/
theorem threaded_run (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck) :
    ∀ fuel, OpenFrame.Run summaries (Mir.JumpThread.jtFunc function)
      ⟨Mir.JumpThread.thread function fuel source.label, source.frame, source.memory⟩ behavior := by
  induction executed with
  | @stop source behavior stopped =>
    show ∀ fuel, OpenFrame.Run summaries (Mir.JumpThread.jtFunc function)
      ⟨Mir.JumpThread.thread function fuel source.label, source.frame, source.memory⟩ behavior
    intro fuel
    rw [thread_fixed (next_none_of_stops summaries stopped successful)]
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨sourceBlock, final, found, actual⟩ := stopped
      exact .stop ⟨threadedBlock function sourceBlock, final, block_found found, block summaries function actual⟩
    | stuck => exact False.elim (successful rfl)
    | diverges => exact False.elim stopped
  | @next source target behavior step rest ih =>
    show ∀ fuel, OpenFrame.Run summaries (Mir.JumpThread.jtFunc function)
      ⟨Mir.JumpThread.thread function fuel source.label, source.frame, source.memory⟩ behavior
    intro fuel
    have current : OpenFrame.Run summaries (Mir.JumpThread.jtFunc function) source behavior :=
      .next (jump summaries step) (ih successful function.blocks.size)
    cases fuel with
    | zero => exact current
    | succ fuel =>
      cases selected : Mir.JumpThread.next function source.label with
      | none => simpa only [Mir.JumpThread.thread, selected] using current
      | some label =>
        have same : target = ⟨label, source.frame, source.memory⟩ := next_step summaries selected step
        subst target
        simpa only [Mir.JumpThread.thread, selected] using ih successful fuel

theorem run (summaries : OpenCalls) {function : Mir.Func} {source : OpenFrame.State} {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck) :
    OpenFrame.Run summaries (Mir.JumpThread.jtFunc function) source behavior :=
  threaded_run summaries executed successful 0

theorem function_call_free {source : Mir.Func} (free : OpenFrame.FunctionCallFree source) :
    OpenFrame.FunctionCallFree (Mir.JumpThread.jtFunc source) := by
  intro label candidate found
  have selected : ∃ block, source.blocks[label]? = some block ∧ threadedBlock source block = candidate := by
    simpa only [Mir.JumpThread.blocks_get, threadedBlock, Option.map_eq_some_iff] using found
  obtain ⟨block, original, rfl⟩ := selected
  exact free label block original

theorem observations_exact (summaries : OpenCalls) {function : Mir.Func}
    (free : OpenFrame.FunctionCallFree function) (source : OpenFrame.State) {behavior : Lir.Behavior}
    (executed : OpenFrame.Run summaries function source behavior) (successful : behavior ≠ .stuck)
    (other : Lir.Behavior) :
    OpenFrame.Behaves summaries (Mir.JumpThread.jtFunc function) source other ↔ other = behavior := by
  have candidate : OpenFrame.Run summaries (Mir.JumpThread.jtFunc function) source behavior := run summaries executed successful
  have candidateFree : OpenFrame.FunctionCallFree (Mir.JumpThread.jtFunc function) := function_call_free free
  constructor
  · intro observed
    cases other with
    | diverges => exact False.elim (OpenFrame.run_no_infinite candidateFree candidate observed)
    | returned values memory | trapped memory | stuck =>
      obtain ⟨final, steps, stopped⟩ := observed
      exact (OpenFrame.run_unique candidateFree candidate (OpenFrame.run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact OpenFrame.run_behaves candidate

end Silmaril.Compiler.Native.Optimize.Open.JumpThread
