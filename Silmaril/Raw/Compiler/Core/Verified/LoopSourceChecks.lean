module

public import Silmaril.Compiler.Core.Verified.LoopIteration.Defs
/-! Kernel checks for counter updates, saved continuations and label aliases. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopSourceChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open StateExpr (Term values)

def x : Sym := ⟨⟨[]⟩, 504, .objectAddress "ret"⟩
def loopLabel : Sym := ⟨⟨[]⟩, 512, .id "while_512"⟩
def labelAlias : Sym := ⟨⟨[]⟩, 512, .none⟩
def unitExpr : EE := .mk [] (.pure (.mk [] () (.val .unit)))

/-- The actual loaded test is `(ret < 10) == 0`, before `z != 1`. -/
def condition : Term := .cmp .eq 1 0 (.cmp .lt 1 0 (.var x.key) (.lit 10)) (.lit 0)

example : condition.val (fun _ => 0) = 0 := by decide
example : (LoopBlocks.coreTest condition).val (fun _ => 0) = 1 := by decide
example : condition.val (fun _ => 10) = 1 := by decide
example : (LoopBlocks.coreTest condition).val (fun _ => 10) = 0 := by decide

/-- The assignment and saved-continue glue after the true test of ci/0055. -/
def body : LoopFallthrough.Stmt :=
  .seq (.seq (.assign x (.bin .add (.var x.key) (.lit 1))) .skip)
    (.seq (.save x .skip) .skip)

/-- Each iteration advances the current value, including after a previous update. -/
example (n : Int) : values (StateMem.defsOf (body.defs (fun _ => some (.lit n)))) x.key = n + 1 := by
  simp [body, LoopFallthrough.Stmt.defs, StateMem.update, StateMem.defsOf,
    values, StateExpr.close_val, StateExpr.Term.val, IntExpr.Term.val, Guard.apply]

example (n : Int) (range : 0 ≤ n ∧ n < 10) :
    body.Valid (fun _ => some (.lit n)) := by
  simp [body, LoopFallthrough.Stmt.Valid, StateExpr.Term.Ok, StateExpr.Term.val,
    values, StateMem.defsOf, IntExpr.Term.val, Guard.apply, ConvInt.IsInt]
  omega

/-- Both the break continuation and enclosing return continuation are retained. -/
def context : LoopContext.Context :=
  .strong [] (.mk [] (.base (none, .unit))) unitExpr
    (.weak [] (.mk [] (.base (none, .unit))) unitExpr .hole)

def saved : EE := .mk [] (.save (loopLabel, .unit) [] unitExpr)

example : (Map.ofList (saves (context.fill saved))).lookup loopLabel =
    some ([], context.fill unitExpr) := by
  exact context.lookup_save [] (loopLabel, .unit) [] unitExpr (by decide)

/-- Symbol descriptions do not distinguish labels in the actual lookup. -/
example : (Map.ofList (saves (context.fill saved))).lookup labelAlias =
    some ([], context.fill unitExpr) := by
  change (Map.ofList (saves (context.fill saved))).lookup loopLabel = _
  exact context.lookup_save [] (loopLabel, .unit) [] unitExpr (by decide)

/-- Dropping the right continuations changes the saved body. -/
example : context.fill unitExpr ≠ unitExpr := by
  intro h
  cases h

/-- Two labels with the same semantic key violate the lookup theorem's premise. -/
example : ¬ ([loopLabel, labelAlias].map (·.key)).Nodup := by decide

end Silmaril.Compile.Core.Verified.LoopSourceChecks
