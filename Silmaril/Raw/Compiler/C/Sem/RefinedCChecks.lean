module

public import Silmaril.Cerberus.Assertion.RefinedC.Defs
public import Silmaril.Compiler.C.Sem.AssertionExecutionChecks.Defs
/-! Concrete refinement checks include representability failures, owned cells, and an
integer-refined return assertion certified by actual typed-Ail C0 execution. -/

@[expose] public section
namespace Silmaril.Cerberus.Assertion.RefinedC.Checks

open Silmaril.Cerberus.Assertion.Pure
open Silmaril.Compile.C.Sem
open Silmaril.Compile.C.Sem.AssertionExecution
open Silmaril.Compile.C.Sem.AssertionExecution.Checks

def emptyEnv : Env := fun _ => 0

def signedByte : IntRefinement := ⟨.i8, none⟩
def unsignedByte : IntRefinement := ⟨.u8, none⟩

theorem signedByte_maximum : signedByte.holds emptyEnv 127 := by
  change (-128 ≤ (127 : Int) ∧ 127 < 128) ∧ True
  decide +kernel

theorem signedByte_overflow_rejected : ¬signedByte.holds emptyEnv 128 := by
  change ¬ ((-128 ≤ (128 : Int) ∧ 128 < 128) ∧ True)
  decide +kernel

theorem unsignedByte_negative_rejected : ¬unsignedByte.holds emptyEnv (-1) := by
  change ¬ ((0 ≤ (-1 : Int) ∧ -1 < 256) ∧ True)
  decide +kernel

/-- The output refinement of an `add1` annotation; source x is supplied by `view`. -/
def incrementReturn : IntRefinement :=
  ⟨.i32, some (.add (.var "x") (.literal 1))⟩

def incrementAssertion : RichFormula :=
  .pure (incrementReturn.toFormula (.var "result"))

/-- The 32-bit return refinement holds on the actual executable invocation, rather
than merely under an assumption that the body computes the specified result. -/
theorem increment_refined_frame_goal :
    FrameGoal program incrementFunction incrementBody
      initial view incrementAssertion := by
  refine ⟨8, some 256, initial, increment_executes, ?_⟩
  change (incrementReturn.toFormula (.var "result")).check
    (view (some 256) initial) = true
  cbv

theorem increment_refined_frame_contract :
    FrameContract program incrementFunction incrementBody
      initial view incrementAssertion :=
  (frameGoal_correct _ _ _ _ _ _).mp increment_refined_frame_goal

/-- Full abstract ownership plus the same signed integer singleton refinement. -/
theorem owned_increment_result :
    (incrementReturn.owned 17 (.literal 256)).leanGoal
      (view (some 256) initial) [(17, 256)] := by
  apply (IntRefinement.ownedGoal_correct _ _ _ _ _).mpr
  constructor
  · apply (incrementReturn.leanGoal_correct _ (.literal 256)).mp
    change (incrementReturn.toFormula (.literal 256)).check
      (view (some 256) initial) = true
    cbv
  · rfl

end Silmaril.Cerberus.Assertion.RefinedC.Checks
