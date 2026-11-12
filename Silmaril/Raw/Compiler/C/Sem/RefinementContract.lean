module

public import Silmaril.Compiler.C.Sem.AssertionExecution.Defs
public import Silmaril.Cerberus.Assertion.RefinedC.Defs
@[expose] public section

/-!
# Function-entry refinement contracts for executable C0

RefinedC combines ownership and refinement types, interprets its typing rules in
Iris, and automates proofs with Lithium (https://plv.mpi-sws.org/refinedc/).
This incremental bridge handles integer refinements at actual C0 function entry.
It does not interpret RefinedC's ownership types or prove equivalence with its
Caesium/Iris semantics. C0's deterministic evaluation and integer conversions apply.

Unlike a body-only statement contract, `C0.callFn` looks up the callee, checks
arity, converts arguments, creates parameter locals, converts the return value,
and restores caller locals. The final state therefore exposes globals/output and
caller locals, not the callee's discarded local frame. A client supplies the view.
Normal finite return is required: UB, unsupported constructs, exhaustion, exit,
and abort do not certify these contracts. No whole-program/backend theorem follows
without a separate linking/context certificate relating this call to process runs.
-/

namespace Silmaril.Compile.C.Sem.RefinementContract

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion.Pure

universe u

/-- Ghost values describe mathematical refinements. Preconditions refer to actual
argument values before C parameter conversion and the actual caller state. -/
structure Spec (Ghost : Type u) where
  pre : Ghost → List Int → C0.Env → Prop
  post : Ghost → List Int → C0.Env → Int → C0.Env → Prop

/-- Every admissible invocation has a finite normal return satisfying the post.
Fuel may depend on the arguments and state; this is a total-correctness contract. -/
def Total {Ghost : Type u} (P : C0.Prog) (callee : Sym) (spec : Spec Ghost) : Prop :=
  ∀ ghost args initial, spec.pre ghost args initial →
    ∃ fuel result finalState,
      C0.callFn P fuel callee args initial = .ok (result, finalState) ∧
      spec.post ghost args initial result finalState

/-- Every ghost refinement has a realizable input, preventing contradictory entry
assumptions from producing a vacuous certificate. -/
def Realizable {Ghost : Type u} (spec : Spec Ghost) : Prop :=
  ∀ ghost, ∃ args initial, spec.pre ghost args initial

/-- The total contract together with realizable parameter refinements. -/
def CheckedTotal {Ghost : Type u} (P : C0.Prog) (callee : Sym) (spec : Spec Ghost) : Prop :=
  Realizable spec ∧ Total P callee spec

/-- Elaborate an assertion through an explicit view of the real call boundary. -/
def assertionSpec {Ghost : Type u}
    (pre : Ghost → List Int → C0.Env → Prop)
    (view : Ghost → List Int → C0.Env → Int → C0.Env → Env)
    (post : RichFormula) : Spec Ghost :=
  ⟨pre, fun ghost args initial result finalState =>
    post.holds (view ghost args initial result finalState)⟩

/-- Generated Lean obligations retain the actual function execution equation. -/
def Goal {Ghost : Type u} (P : C0.Prog) (callee : Sym)
    (pre : Ghost → List Int → C0.Env → Prop)
    (view : Ghost → List Int → C0.Env → Int → C0.Env → Env)
    (post : RichFormula) : Prop :=
  ∀ ghost args initial, pre ghost args initial →
    ∃ fuel result finalState,
      C0.callFn P fuel callee args initial = .ok (result, finalState) ∧
      post.leanGoal (view ghost args initial result finalState)

theorem goal_correct {Ghost : Type u} (P : C0.Prog) (callee : Sym)
    (pre : Ghost → List Int → C0.Env → Prop)
    (view : Ghost → List Int → C0.Env → Int → C0.Env → Env) (post : RichFormula) :
    Goal P callee pre view post ↔ Total P callee (assertionSpec pre view post) := by
  simp only [Goal, Total, assertionSpec, RichFormula.leanGoal_correct]

/-- Connect elaborated RefinedC integer annotations to the actual call semantics.
The before/after valuations are explicit; this does not infer a source-name map. -/
def refinedCSpec {Ghost : Type u} (annotation : Silmaril.Cerberus.Assertion.RefinedC.Contract)
    (before : Ghost → List Int → C0.Env → Env)
    (after : Ghost → List Int → C0.Env → Int → C0.Env → Env) : Spec Ghost where
  pre ghost args initial := annotation.pre (before ghost args initial) args
  post ghost args initial result finalState :=
    annotation.post (after ghost args initial result finalState) result

/-- A total execution witness and an annotation solver goal suffice for the call
contract. The execution premise is indispensable and is retained explicitly. -/
theorem refinedC_total_of_goals {Ghost : Type u} (P : C0.Prog) (callee : Sym)
    (annotation : Silmaril.Cerberus.Assertion.RefinedC.Contract)
    (before : Ghost → List Int → C0.Env → Env)
    (after : Ghost → List Int → C0.Env → Int → C0.Env → Env)
    (certificate : ∀ ghost args initial,
      annotation.pre (before ghost args initial) args →
      ∃ fuel result finalState,
        C0.callFn P fuel callee args initial = .ok (result, finalState) ∧
        annotation.leanGoal (before ghost args initial)
          (after ghost args initial result finalState) args result) :
    Total P callee (refinedCSpec annotation before after) := by
  intro ghost args initial hp
  obtain ⟨fuel, result, finalState, run, goal⟩ := certificate ghost args initial hp
  exact ⟨fuel, result, finalState, run,
    (Silmaril.Cerberus.Assertion.RefinedC.Contract.leanGoal_correct _ _ _ _ _).mp goal hp⟩

/-- A proved call contract can be weakened without rerunning the interpreter. -/
theorem Total.weaken {Ghost : Type u} {P : C0.Prog} {callee : Sym}
    {s t : Spec Ghost} (h : Total P callee s)
    (hp : ∀ g a e, t.pre g a e → s.pre g a e)
    (hq : ∀ g a e r f, t.pre g a e → s.post g a e r f → t.post g a e r f) :
    Total P callee t := by
  intro g a e ht
  obtain ⟨fuel, r, f, run, post⟩ := h g a e (hp g a e ht)
  exact ⟨fuel, r, f, run, hq g a e r f ht post⟩

end Silmaril.Compile.C.Sem.RefinementContract
