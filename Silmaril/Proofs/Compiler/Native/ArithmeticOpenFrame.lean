module

public import Silmaril.Compiler.Native.Correctness.ArithmeticOpenFrame.Defs
public import Silmaril.Compiler.Native.Correctness.ArithmeticLower.Thms
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.ArithmeticOpenFrame
open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Core.SignedArithmetic
open Silmaril.Compiler.Native Silmaril.Compiler.Native.Semantics
open Silmaril.Compiler.Native.Correctness.ArithmeticLower

theorem actual_start (expression : Expression) (memory : Lir.Memory) :
    OpenFrame.start (artifact expression) "main" [] memory = some (invocation expression memory) := rfl

theorem prologue_step (expression : Expression) (environment : OpenFrame.Environment) (memory : Lir.Memory) :
    OpenFrame.Step (OpenFrame.calls (artifact expression) environment) (function expression)
      (initial memory) (afterPrologue environment memory) := by
  apply OpenFrame.Step.jump (block := AdditionLower.prologue) rfl
  exact AdditionLower.prologue_executed _ _ _ _ (OpenFrame.reserved_address _ _ _)

theorem actual_run (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) :
    OpenFrame.Run (OpenFrame.calls (artifact expression) environment) (function expression)
      (initial memory) (.returned [BitVec.ofInt 64 expression.value] memory) := by
  refine .next (prologue_step expression environment memory) (.stop ?_)
  exact ⟨body expression, bodyFrame expression (afterPrologue environment memory).frame,
    rfl, body_executed expression bounded _ _ memory⟩

theorem plan_call_free (expression : Expression) (next : Nat) :
    ∀ instruction ∈ (plan expression next).instructions, OpenFrame.CallFree instruction := by
  induction expression generalizing next with
  | literal number => simp [plan, OpenFrame.CallFree]
  | binary operator left right first last =>
    intro instruction member
    simp only [plan, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (member | member) | rfl | rfl | rfl | rfl
    · exact first next instruction member
    · exact last (plan left next).nextReg instruction member
    all_goals trivial

theorem body_call_free (expression : Expression) : OpenFrame.BlockCallFree (body expression) := by
  intro instruction member
  simp only [body, Array.toList_push, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with member | rfl
  · exact plan_call_free expression 2 instruction member
  · trivial

theorem actual_call_free (expression : Expression) : OpenFrame.FunctionCallFree (function expression) := by
  intro label block found
  have labelBound : label < 3 := by
    have bounded := (Array.getElem?_eq_some_iff).mp found
    simpa [function] using bounded.1
  interval_cases label
  · simp [function] at found
    subst block
    simp [AdditionLower.prologue, OpenFrame.BlockCallFree, OpenFrame.CallFree]
  · simp [function] at found
    subst block
    exact body_call_free expression
  · simp [function] at found
    subst block
    simp [AdditionLower.fallback, OpenFrame.BlockCallFree, OpenFrame.CallFree]

/-- All observations of the actual function are determined by its derived
finite run and independent syntactic call freedom. -/
theorem function_observations_exact (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves (OpenFrame.calls (artifact expression) environment) (function expression)
      (initial memory) behavior ↔ behavior = .returned [BitVec.ofInt 64 expression.value] memory :=
  OpenFrame.run_observations_exact (actual_call_free expression) (actual_run expression bounded environment memory) behavior

theorem artifact_observations_exact (expression : Expression) (bounded : expression.Bounded)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes (artifact expression) environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory := by
  constructor
  · rintro ⟨candidate, started, executed⟩
    have same := Option.some.inj ((actual_start expression memory).symm.trans started)
    subst candidate
    exact (function_observations_exact expression bounded environment memory behavior).1 executed
  · intro expected
    exact ⟨invocation expression memory, actual_start expression memory,
      (function_observations_exact expression bounded environment memory behavior).2 expected⟩

/-- Actual successful lowering is derived from the bounded typed-Ail source,
then interpreted by the unchanged named Artifact invocation. -/
theorem compiled_observations_exact (expression : Expression) (bounded : expression.Bounded)
    (tag : String) (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    (∃ result, Lower.compile tag (Main.program expression) = .ok result ∧
      OpenFrame.Observes result environment "main" [] memory behavior) ↔
      behavior = .returned [BitVec.ofInt 64 expression.value] memory := by
  constructor
  · rintro ⟨result, compiled, observed⟩
    have same := Except.ok.inj ((ArithmeticLower.compile expression bounded tag).symm.trans compiled)
    subst result
    exact (artifact_observations_exact expression bounded environment memory behavior).1 observed
  · intro expected
    exact ⟨_, ArithmeticLower.compile expression bounded tag,
      (artifact_observations_exact expression bounded environment memory behavior).2 expected⟩

end Silmaril.Compiler.Native.Correctness.ArithmeticOpenFrame
