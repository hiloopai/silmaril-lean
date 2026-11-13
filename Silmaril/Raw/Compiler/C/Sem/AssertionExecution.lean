module

public import Silmaril.Cerberus.Assertion.Pure.Defs
public import Silmaril.Compiler.C.Sem.C0Mono.Defs
@[expose] public section

/-!
# Assertion goals over executable typed Ail

A successful C0 run certifies a whole-program postcondition. The result exposed here is
explicitly the process exit status modulo 256, not a function's mathematical return value.
Signals and divergence do not satisfy these postconditions. Requiring a successful run
excludes certificates obtained from unsupported programs, fuel exhaustion or UB alone.

For assertions about activation-body returns and local variables use `FrameContract`:
its view of the final interpreter state is supplied explicitly by the client, rather than
assuming a source-name mapping or inventing values for uninitialized locals.
-/

namespace Silmaril.Compile.C.Sem.AssertionExecution

open Silmaril.Cerberus.Assertion.Pure
open Silmaril.Cerberus.Ail

/-- The two observable integer names at the process boundary. Other names denote zero;
clients should use only these names, or explicitly choose another observation view. -/
def processEnv (status bytes : Nat) : Env := fun name =>
  if name = "exit_status" then (status : Int)
  else if name = "stdout_length" then (bytes : Int) else 0

/-- A normal process exit whose observation satisfies the elaborated assertion. -/
def ProcessPost (assertion : Formula) (o : Obs) : Prop :=
  ∃ status, o.exit = .status status ∧ assertion.holds (processEnv status o.stdout.length)

/-- The executable Boolean backend's obligation on the same observation. -/
def ProcessGoal (assertion : Formula) (o : Obs) : Prop :=
  ∃ status, o.exit = .status status ∧ assertion.leanGoal (processEnv status o.stdout.length)

theorem processGoal_correct (assertion : Formula) (o : Obs) :
    ProcessGoal assertion o ↔ ProcessPost assertion o := by
  simp only [ProcessGoal, ProcessPost, Formula.leanGoal_correct]

/-- A completed run determines every C0 behaviour, including at other fuel bounds.
The UB-closed semantics cannot produce additional observations after this certificate. -/
theorem beh_iff_of_done {p : TypedProgram} {fuel : Nat} {o : Obs}
    (h : C0.run fuel p = .done o) (o' : Obs) : o' ∈ C0.beh p ↔ o' = o := by
  constructor
  · intro hb
    rcases hb with ⟨n, hn⟩ | ⟨n, why, hn⟩ | ⟨_, hn⟩
    · have he := C0.run_agree hn h (by intro he; cases he) (by intro he; cases he)
      cases he
      rfl
    · have he := C0.run_agree hn h (by intro he; cases he) (by intro he; cases he)
      cases he
    · have he := (hn fuel).symm.trans h
      cases he
  · intro he
    subst o'
    exact C0.beh_of_done h

/-- A certificate is non-vacuous and implies a universal assertion about the unbounded
C0 behaviour set, rather than merely about one bounded execution. -/
theorem process_goal_iff_sat {p : TypedProgram} {fuel : Nat} {o : Obs}
    (run : C0.run fuel p = .done o) (assertion : Formula) :
    ProcessGoal assertion o ↔ C0.lang.Sat p {o | ProcessPost assertion o} := by
  rw [processGoal_correct]
  constructor
  · intro hp o' ho'
    rw [(beh_iff_of_done run o').mp ho']
    exact hp
  · intro hp
    exact hp (C0.beh_of_done run)

/-- A successful Ail activation-body evaluation together with its assertion goal. The interpreter
execution is part of the obligation, so a prover cannot certify a postcondition by
assuming that an arbitrary expression evaluated to the desired result. -/
def FrameGoal (P : C0.Prog) (fd : C0.FunDef) (body : TypedStatement)
    (initial : C0.Env) (view : Option Int → C0.Env → Env) (post : RichFormula) : Prop :=
  ∃ fuel result finalState,
    C0.loop P fuel fd (some body) .stop initial = .ok (result, finalState) ∧
    post.leanGoal (view result finalState)

/-- Total correctness for this activation body in the deterministic C0 interpreter:
a normal, finite execution with an assertion on its body return and final store.
The supplied `view` must be justified separately when relating source variable names.
Function entry, argument conversion, and consistency of `body` with `fd.body` are
client obligations; this judgment describes `loop` rather than `callFn`. -/
def FrameContract (P : C0.Prog) (fd : C0.FunDef) (body : TypedStatement)
    (initial : C0.Env) (view : Option Int → C0.Env → Env) (post : RichFormula) : Prop :=
  ∃ fuel result finalState,
    C0.loop P fuel fd (some body) .stop initial = .ok (result, finalState) ∧
    post.holds (view result finalState)

theorem frameGoal_correct (P : C0.Prog) (fd : C0.FunDef) (body : TypedStatement)
    (initial : C0.Env) (view : Option Int → C0.Env → Env) (post : RichFormula) :
    FrameGoal P fd body initial view post ↔ FrameContract P fd body initial view post := by
  simp only [FrameGoal, FrameContract, RichFormula.leanGoal_correct]

end Silmaril.Compile.C.Sem.AssertionExecution
