module

public import Silmaril.Compiler.Native.Correctness.AdditionOpenFrame.Defs
public import Silmaril.Compiler.Native.Semantics.OpenFrame.Thms
public import Silmaril.Compiler.Native.Correctness.AdditionLower.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.AdditionOpenFrame

open Silmaril.Compile Silmaril.Machine
open Silmaril.Compiler.Native.Semantics
open Silmaril.Compiler.Native.Optimize

theorem actual_start (left right : Lir.Word) (memory : Lir.Memory) :
    OpenFrame.start (AdditionLower.artifact left right) "main" [] memory =
      some (invocation left right memory) := rfl

theorem prologue_step (left right : Lir.Word) (environment : OpenFrame.Environment)
    (memory : Lir.Memory) :
    OpenFrame.Step (OpenFrame.calls (AdditionLower.artifact left right) environment)
      (AdditionLower.function left right) (initial memory) (afterPrologue environment memory) := by
  apply OpenFrame.Step.jump (block := AdditionLower.prologue) rfl
  exact AdditionLower.prologue_executed _ _ _ _ (OpenFrame.reserved_address _ _ _)

theorem actual_run (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) :
    OpenFrame.Run
      (OpenFrame.calls (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
      (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) (initial memory)
      (.returned [BitVec.ofInt 64 (left + right)] memory) := by
  refine .next (prologue_step _ _ environment memory) (.stop ?_)
  refine ⟨AdditionLower.body _ _,
    AdditionLower.bodyFrame (afterPrologue environment memory).frame
      (BitVec.ofInt 64 left) (BitVec.ofInt 64 right), rfl, ?_⟩
  exact AdditionLower.body_executed _ _ memory left right bounds

theorem actual_call_free (left right : Lir.Word) :
    OpenFrame.FunctionCallFree (AdditionLower.function left right) := by
  intro label block found
  have labelBound : label < 3 := by
    have bounded := (Array.getElem?_eq_some_iff).mp found
    simpa [AdditionLower.function] using bounded.1
  interval_cases label <;>
    simp [AdditionLower.function, AdditionLower.prologue, AdditionLower.body, AdditionLower.fallback] at found <;>
    subst block <;>
    simp [OpenFrame.BlockCallFree, OpenFrame.CallFree]

/-- Every observation follows the actual block semantics. Stuckness, trapping,
divergence and alternate returned memories/values are all excluded by the run
and the independently checked absence of calls. No target trace is assumed. -/
theorem function_observations_exact (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Behaves
        (OpenFrame.calls (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) environment)
        (AdditionLower.function (BitVec.ofInt 64 left) (BitVec.ofInt 64 right)) (initial memory) behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory :=
  OpenFrame.run_observations_exact (actual_call_free _ _) (actual_run left right bounds environment memory) behavior

theorem artifact_observations_exact (left right : Int) (bounds : AdditionSource.Bounds left right)
    (environment : OpenFrame.Environment) (memory : Lir.Memory) (behavior : Lir.Behavior) :
    OpenFrame.Observes
        (AdditionLower.artifact (BitVec.ofInt 64 left) (BitVec.ofInt 64 right))
        environment "main" [] memory behavior ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory := by
  constructor
  · rintro ⟨candidate, started, executed⟩
    have same := Option.some.inj ((actual_start _ _ memory).symm.trans started)
    subst candidate
    exact (function_observations_exact left right bounds environment memory behavior).1 executed
  · intro expected
    exact ⟨invocation _ _ memory, actual_start _ _ memory,
      (function_observations_exact left right bounds environment memory behavior).2 expected⟩

/-- Successful compilation is derived from the independent bounded input;
the actual output is then interpreted by the explicit open-frame semantics. -/
theorem compiled_observations_exact (left right : Int) (bounds : AdditionSource.Bounds left right)
    (tag : String) (environment : OpenFrame.Environment) (memory : Lir.Memory)
    (behavior : Lir.Behavior) :
    (∃ artifact, Silmaril.Compiler.Native.Lower.compile tag (AdditionSource.program left right) = .ok artifact ∧
      OpenFrame.Observes artifact environment "main" [] memory behavior) ↔
      behavior = .returned [BitVec.ofInt 64 (left + right)] memory := by
  constructor
  · rintro ⟨artifact, compiled, observed⟩
    have same := Except.ok.inj ((AdditionLower.compile left right bounds tag).symm.trans compiled)
    subst artifact
    exact (artifact_observations_exact left right bounds environment memory behavior).1 observed
  · intro expected
    exact ⟨_, AdditionLower.compile left right bounds tag,
      (artifact_observations_exact left right bounds environment memory behavior).2 expected⟩

end Silmaril.Compiler.Native.Correctness.AdditionOpenFrame
