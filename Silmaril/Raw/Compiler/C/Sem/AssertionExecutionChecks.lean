module

public import Silmaril.Compiler.C.Sem.AssertionExecution.Defs
/-! Concrete checks connect elaborated assertions to typed-Ail execution, distinguishing
an integer function return from the process exit status modulo 256. -/

@[expose] public section
namespace Silmaril.Compile.C.Sem.AssertionExecution.Checks

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Cerberus.Assertion.Pure

def xSym : Sym := ⟨⟨[]⟩, 0, .id "x"⟩
def intAnnot : GenTypeCategory := .rvalue (.basic (.integer (.concrete (.signed .int))))
def intExpr (node : ExpressionNode GenTypeCategory) : TypedExpression :=
  .mk intAnnot [] .unknown node
def literal (n : Int) : TypedExpression :=
  intExpr (.const (.integer (.iconstant n .decimal none)))
def xLvalue : TypedExpression :=
  .mk (.lvalue ⟨false, false, false⟩ (.mk [] (.basic (.integer (.signed .int)))) false)
    [] .unknown (.ident xSym)
def incrementBody : TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk [])
    (.return_ (intExpr (.binary (intExpr (.rvalue xLvalue)) (.arithmetic .add) (literal 1))))
def incrementFunction : C0.FunDef :=
  ⟨[(0, .int 4 true)], .int 4 true, incrementBody, {}⟩
def program : C0.Prog := ⟨{}, {}, {}, [], ∅, none⟩
def initial : C0.Env := { locals := ({} : Std.HashMap Nat Int).insert 0 255 }

/-- Explicit source-name view: result is the raw function return; x reads local slot 0. -/
def view (result : Option Int) (state : C0.Env) : Env := fun name =>
  if name = "result" then result.getD 0 else
  if name = "x" then (state.locals[0]?).getD 0 else 0

def incrementPost : RichFormula := .pure
  (.and (.eq (.var "result") (.add (.var "x") (.literal 1)))
    (.eq (.var "result") (.literal 256)))

/-- The interpreter reads x, checks signed addition, and returns the raw integer 256. -/
theorem increment_executes :
    C0.loop program 8 incrementFunction (some incrementBody) .stop initial =
      .ok (some 256, initial) := by
  cbv

theorem increment_frame_goal :
    FrameGoal program incrementFunction incrementBody initial view incrementPost := by
  exact ⟨8, some 256, initial, increment_executes, by
    apply (RichFormula.leanGoal_correct _ _).mpr
    simp [incrementPost, RichFormula.holds, Formula.holds, Term.eval, view, initial]⟩

theorem increment_frame_contract :
    FrameContract program incrementFunction incrementBody initial view incrementPost :=
  (frameGoal_correct _ _ _ _ _ _).mp increment_frame_goal

def zeroExit : Obs := ⟨[], .status 0⟩
def processZero : Formula := .eq (.var "exit_status") (.literal 0)
def process256 : Formula := .eq (.var "exit_status") (.literal 256)

theorem zero_exit_goal : ProcessGoal processZero zeroExit := by
  exact ⟨0, rfl, by rfl⟩

/-- A raw return of 256 must not be mistaken for observable process status 256. -/
theorem process256_rejected : ¬ ProcessGoal process256 zeroExit := by
  rintro ⟨status, hs, hp⟩
  cases hs
  exact (by decide +kernel : ¬ process256.check (processEnv 0 0) = true) hp

/-- Abnormal termination cannot satisfy a process assertion, even `true`. -/
theorem signal_rejected : ¬ ProcessGoal .truth ⟨[], .signal 6⟩ := by
  rintro ⟨status, hs, _⟩
  cases hs

end Silmaril.Compile.C.Sem.AssertionExecution.Checks
