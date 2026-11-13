module

public import Silmaril.Compiler.Native.Semantics.OpenFrame.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
@[expose] public section
namespace Silmaril.Compiler.Native.Semantics.OpenFrame

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Optimize

theorem reserved_address (artifact : Artifact) (environment : Environment) (offset : Nat) :
    (calls artifact environment).address frameSymbol offset = some environment.frameAddress := by
  simp [calls]

theorem ordinary_address (artifact : Artifact) (environment : Environment)
    (symbol : String) (offset : Nat) (ordinary : symbol ≠ frameSymbol) :
    (calls artifact environment).address symbol offset = environment.address symbol offset := by
  simp [calls, ordinary]

theorem direct_summary (artifact : Artifact) (environment : Environment) (symbol : String)
    (arguments returned : List Lir.Word) (memory finalMemory : Lir.Memory) :
    (calls artifact environment).direct symbol arguments memory returned finalMemory ↔
      environment.direct (artifact.calls.find? (·.key == symbol)) symbol
        arguments memory returned finalMemory := Iff.rfl

theorem returned_of_block (summaries : OpenCalls) (function : Mir.Func) (source : State)
    (block : Mir.Block) (values : List Lir.Word) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (found : function.blocks[source.label]? = some block)
    (executed : BlockExec summaries block source.frame source.memory (.returned values) frame memory) :
    Behaves summaries function source (.returned values memory) := by
  exact ⟨source, .refl, block, frame, found, executed⟩

theorem jump_then (summaries : OpenCalls) (function : Mir.Func) (source target : State)
    (step : Step summaries function source target) (behavior : Lir.Behavior)
    (executed : Behaves summaries function target behavior) :
    Behaves summaries function source behavior := by
  cases behavior with
  | returned values memory | trapped memory | stuck =>
    obtain ⟨final, steps, stopped⟩ := executed
    exact ⟨final, steps.head step, stopped⟩
  | diverges =>
    rcases executed with ⟨trace, first, next⟩
    refine ⟨fun n => match n with | 0 => source | n + 1 => trace n, rfl, ?_⟩
    intro n
    cases n with
    | zero => simpa only [first] using step
    | succ n => exact next n

theorem instruction_unique {summaries : OpenCalls} {instruction : Mir.Instr}
    (callFree : CallFree instruction) {source left right : Lir.Frame Nat}
    {memory leftMemory rightMemory : Lir.Memory}
    (first : InstructionExec summaries instruction source memory left leftMemory)
    (second : InstructionExec summaries instruction source memory right rightMemory) :
    left = right ∧ leftMemory = rightMemory := by
  cases first with
  | op first =>
    cases second with
    | op second => simpa [first] using second
  | fop first =>
    cases second with
    | fop second => exact ⟨Option.some.inj (first.symm.trans second), rfl⟩
  | addr first =>
    cases second with
    | addr second => exact ⟨congrArg (source.set _) (Option.some.inj (first.symm.trans second)), rfl⟩
  | call _ _ _ => exact False.elim callFree
  | indirect _ _ _ _ => exact False.elim callFree

theorem instructions_unique {summaries : OpenCalls} {instructions : List Mir.Instr}
    (callFree : ∀ instruction ∈ instructions, CallFree instruction)
    {source left right : Lir.Frame Nat} {memory leftMemory rightMemory : Lir.Memory}
    (first : InstructionsExec summaries instructions source memory left leftMemory)
    (second : InstructionsExec summaries instructions source memory right rightMemory) :
    left = right ∧ leftMemory = rightMemory := by
  induction first generalizing right rightMemory with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | @cons instruction rest source memory middle middleMem left leftMemory first restFirst ih =>
    cases second with
    | cons second restSecond =>
      obtain ⟨rfl, rfl⟩ := instruction_unique (callFree _ (by simp)) first second
      exact ih (fun instruction member => callFree instruction (by simp [member])) restSecond

theorem term_unique {term : Lir.Term Nat} {source : Lir.Frame Nat} {left right : BlockExit}
    (first : TermExec term source left) (second : TermExec term source right) : left = right := by
  cases first <;> cases second <;> simp_all

theorem block_unique {summaries : OpenCalls} {block : Mir.Block}
    (callFree : BlockCallFree block) {source left right : Lir.Frame Nat}
    {memory leftMemory rightMemory : Lir.Memory} {leftExit rightExit : BlockExit}
    (first : BlockExec summaries block source memory leftExit left leftMemory)
    (second : BlockExec summaries block source memory rightExit right rightMemory) :
    leftExit = rightExit ∧ left = right ∧ leftMemory = rightMemory := by
  obtain ⟨rfl, rfl⟩ := instructions_unique callFree first.1 second.1
  exact ⟨term_unique first.2 second.2, rfl, rfl⟩

theorem step_unique {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source left right : State}
    (first : Step summaries function source left) (second : Step summaries function source right) :
    left = right := by
  cases first with
  | jump found first =>
    cases second with
    | jump otherFound second =>
      have same := Option.some.inj (found.symm.trans otherFound)
      subst same
      obtain ⟨sameExit, rfl, rfl⟩ := block_unique (callFree _ _ found) first second
      cases sameExit
      rfl

theorem step_stops_false {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source target : State}
    (step : Step summaries function source target) {behavior : Lir.Behavior}
    (stopped : Stops summaries function source behavior) : False := by
  cases step with
  | jump found executed =>
    cases behavior with
    | returned values memory | trapped memory =>
      obtain ⟨block, frame, otherFound, otherRun⟩ := stopped
      have same := Option.some.inj (found.symm.trans otherFound)
      subst same
      have exits := (block_unique (callFree _ _ found) executed otherRun).1
      cases exits
    | stuck => exact stopped _ found ⟨_, _, _, executed⟩
    | diverges => exact stopped

theorem stops_unique {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source : State} {left right : Lir.Behavior}
    (first : Stops summaries function source left) (second : Stops summaries function source right) :
    left = right := by
  cases left with
  | diverges => exact False.elim first
  | stuck =>
    cases right with
    | stuck => rfl
    | diverges => exact False.elim second
    | returned values memory | trapped memory =>
      obtain ⟨block, frame, found, executed⟩ := second
      exact False.elim (first block found ⟨_, _, _, executed⟩)
  | returned values memory | trapped memory =>
    show _ = right
    obtain ⟨block, frame, found, executed⟩ := first
    cases right with
    | diverges => exact False.elim second
    | stuck => exact False.elim (second block found ⟨_, _, _, executed⟩)
    | returned otherValues otherMemory | trapped otherMemory =>
      obtain ⟨otherBlock, otherFrame, otherFound, otherRun⟩ := second
      have same : block = otherBlock := Option.some.inj (found.symm.trans otherFound)
      subst same
      obtain ⟨exits, _, memories⟩ := block_unique (callFree _ _ found) executed otherRun
      cases exits ; all_goals cases memories ; all_goals rfl

theorem run_prepend {summaries : OpenCalls} {function : Mir.Func}
    {source target : State} (steps : Relation.ReflTransGen (Step summaries function) source target)
    {behavior : Lir.Behavior} (rest : Run summaries function target behavior) :
    Run summaries function source behavior := by
  induction steps with
  | refl => exact rest
  | tail steps step ih => exact ih (.next step rest)

theorem run_unique {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source : State} {left right : Lir.Behavior}
    (first : Run summaries function source left) (second : Run summaries function source right) :
    left = right := by
  induction first with
  | stop first =>
    cases second with
    | stop second => exact stops_unique callFree first second
    | next step _ => exact False.elim (step_stops_false callFree step first)
  | next step rest ih =>
    cases second with
    | stop second => exact False.elim (step_stops_false callFree step second)
    | next otherStep otherRun =>
      have same := step_unique callFree step otherStep
      subst same
      exact ih otherRun

theorem run_no_infinite {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source : State} {behavior : Lir.Behavior}
    (run : Run summaries function source behavior) :
    ¬ Silmaril.InfiniteTrace (Step summaries function) source := by
  induction run with
  | stop stopped =>
    rintro ⟨trace, first, next⟩
    have step := next 0
    rw [first] at step
    exact step_stops_false callFree step stopped
  | next step rest ih =>
    rintro ⟨trace, first, next⟩
    have firstStep := next 0
    rw [first] at firstStep
    have same := step_unique callFree step firstStep
    exact ih ⟨fun n => trace (n + 1), same.symm, fun n => next (n + 1)⟩

theorem run_behaves {summaries : OpenCalls} {function : Mir.Func}
    {source : State} {behavior : Lir.Behavior} (run : Run summaries function source behavior) :
    Behaves summaries function source behavior := by
  induction run with
  | @stop source behavior stopped =>
    cases behavior with
    | diverges => exact False.elim stopped
    | returned values memory | trapped memory | stuck => exact ⟨_, .refl, stopped⟩
  | next step rest ih => exact jump_then _ _ _ _ step _ ih

theorem run_observations_exact {summaries : OpenCalls} {function : Mir.Func}
    (callFree : FunctionCallFree function) {source : State} {values : List Lir.Word}
    {memory : Lir.Memory} (run : Run summaries function source (.returned values memory))
    (behavior : Lir.Behavior) :
    Behaves summaries function source behavior ↔ behavior = .returned values memory := by
  constructor
  · intro other
    cases behavior with
    | diverges => exact False.elim (run_no_infinite callFree run other)
    | returned otherValues otherMemory | trapped otherMemory | stuck =>
      obtain ⟨final, steps, stopped⟩ := other
      exact (run_unique callFree run (run_prepend steps (.stop stopped))).symm
  · rintro rfl
    exact run_behaves run

end Silmaril.Compiler.Native.Semantics.OpenFrame
