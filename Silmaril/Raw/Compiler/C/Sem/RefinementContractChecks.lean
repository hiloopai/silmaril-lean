module

public import Silmaril.Compiler.C.Sem.RefinementContract.Defs
public import Silmaril.Compiler.C.Sem.AssertionExecutionChecks.Defs
@[expose] public section

namespace Silmaril.Compile.C.Sem.RefinementContract.Checks

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open AssertionExecution.Checks

/-- The function table is populated, so this example enters through real lookup,
parameter conversion, fresh locals, body evaluation and return conversion. -/
def incrementProgram : C0.Prog :=
  { program with funcs := ({} : Std.HashMap Nat C0.FunDef).insert xSym.number incrementFunction }

def caller : C0.Env := { locals := ({} : Std.HashMap Nat Int).insert 0 17 }

/-- Calling add1(255) returns the raw 256 and restores the caller's x=17.
A body-only proof in an environment where x=255 cannot establish this boundary. -/
theorem increment_call :
    C0.callFn incrementProgram 9 xSym [255] caller = .ok (256, caller) := by
  cbv

def incrementSpec : Spec Unit where
  pre _ args initial := args = [255] ∧ initial = caller
  post _ _ initial result finalState := result = 256 ∧ finalState = initial

theorem increment_checked : CheckedTotal incrementProgram xSym incrementSpec := by
  constructor
  · intro _
    exact ⟨[255], caller, rfl, rfl⟩
  · intro _ args initial h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨9, 256, caller, increment_call, rfl, rfl⟩

/-- The source parameter comes from the input arguments, since callee locals have
been discarded at the return boundary. The returned value comes from the execution. -/
def callView (_ : Unit) (args : List Int) (_ : C0.Env) (result : Int) (_ : C0.Env) :
    Silmaril.Cerberus.Assertion.Pure.Env := fun name =>
  if name = "result" then result else if name = "x" then args.headD 0 else 0

theorem increment_goal :
    Goal incrementProgram xSym incrementSpec.pre callView incrementPost := by
  intro _ args initial h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨9, 256, caller, increment_call, ?_⟩
  apply (Silmaril.Cerberus.Assertion.Pure.RichFormula.leanGoal_correct _ _).mpr
  simp [incrementPost, Silmaril.Cerberus.Assertion.Pure.RichFormula.holds,
    Silmaril.Cerberus.Assertion.Pure.Formula.holds,
    Silmaril.Cerberus.Assertion.Pure.Term.eval, callView]

/-- C parameter conversion is operationally relevant: _Bool maps input 255 to 1. -/
def boolFunction : C0.FunDef :=
  { incrementFunction with params := [(0, .bool)] }
def boolProgram : C0.Prog :=
  { program with funcs := ({} : Std.HashMap Nat C0.FunDef).insert xSym.number boolFunction }

theorem bool_parameter_conversion :
    C0.callFn boolProgram 9 xSym [255] caller = .ok (2, caller) := by
  cbv

/-- Wrong arity is rejected rather than silently satisfying a return assertion. -/
theorem wrong_arity :
    ∀ result finalState, C0.callFn incrementProgram 9 xSym [] caller ≠ .ok (result, finalState) := by
  intro result finalState h
  cbv at h
  cases h

end Silmaril.Compile.C.Sem.RefinementContract.Checks
