module

public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Tauto

/-! A common mathematical-integer assertion fragment for ACSL and CN.
This is an elaborated assertion language, not a parser for either surface language.
C machine arithmetic, loads, ownership and undefined behavior are deliberately absent:
clients must establish that their environment represents the relevant execution state. -/

@[expose] public section
namespace Silmaril.Cerberus.Assertion.Pure

abbrev Env := String → Int

inductive Term where
  | literal : Int → Term
  | var : String → Term
  | add : Term → Term → Term
  | sub : Term → Term → Term
  | mul : Term → Term → Term
  deriving Repr, DecidableEq

def Term.eval (ρ : Env) : Term → Int
  | .literal n => n
  | .var x => ρ x
  | .add a b => a.eval ρ + b.eval ρ
  | .sub a b => a.eval ρ - b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

inductive Formula where
  | truth | falsity
  | eq : Term → Term → Formula
  | le : Term → Term → Formula
  | lt : Term → Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  deriving Repr, DecidableEq

/-- Declarative source-assertion semantics. -/
def Formula.holds (ρ : Env) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .eq a b => a.eval ρ = b.eval ρ
  | .le a b => a.eval ρ ≤ b.eval ρ
  | .lt a b => a.eval ρ < b.eval ρ
  | .not p => ¬p.holds ρ
  | .and p q => p.holds ρ ∧ q.holds ρ
  | .or p q => p.holds ρ ∨ q.holds ρ
  | .implies p q => p.holds ρ → q.holds ρ

/-- Executable assertion checker, independently defined by Boolean operations. -/
def Formula.check (ρ : Env) : Formula → Bool
  | .truth => true
  | .falsity => false
  | .eq a b => decide (a.eval ρ = b.eval ρ)
  | .le a b => decide (a.eval ρ ≤ b.eval ρ)
  | .lt a b => decide (a.eval ρ < b.eval ρ)
  | .not p => !(p.check ρ)
  | .and p q => p.check ρ && q.check ρ
  | .or p q => p.check ρ || q.check ρ
  | .implies p q => !(p.check ρ) || q.check ρ

theorem Formula.check_correct (ρ : Env) (p : Formula) :
    p.check ρ = true ↔ p.holds ρ := by
  induction p <;> simp_all [check, holds, Bool.or_eq_true, Bool.and_eq_true, Bool.eq_false_iff]
  tauto

/-- The proposition emitted as a Lean proof obligation by a Boolean backend. -/
def Formula.leanGoal (ρ : Env) (p : Formula) : Prop := p.check ρ = true

theorem Formula.leanGoal_correct (ρ : Env) (p : Formula) :
    p.leanGoal ρ ↔ p.holds ρ := p.check_correct ρ

/-- A larger layer adds unbounded mathematical-integer quantification.
The pure fragment remains executable; the quantified layer is proposition-valued. -/
inductive RichFormula where
  | pure : Formula → RichFormula
  | and : RichFormula → RichFormula → RichFormula
  | implies : RichFormula → RichFormula → RichFormula
  | all : String → RichFormula → RichFormula
  | ex : String → RichFormula → RichFormula
  deriving Repr, DecidableEq

def bind (ρ : Env) (x : String) (n : Int) : Env :=
  fun y => if y = x then n else ρ y

def RichFormula.holds (ρ : Env) : RichFormula → Prop
  | .pure p => p.holds ρ
  | .and p q => p.holds ρ ∧ q.holds ρ
  | .implies p q => p.holds ρ → q.holds ρ
  | .all x p => ∀ n : Int, p.holds (bind ρ x n)
  | .ex x p => ∃ n : Int, p.holds (bind ρ x n)

/-- Translate larger assertions structurally to Lean, checking pure leaves. -/
def RichFormula.leanGoal (ρ : Env) : RichFormula → Prop
  | .pure p => p.leanGoal ρ
  | .and p q => p.leanGoal ρ ∧ q.leanGoal ρ
  | .implies p q => p.leanGoal ρ → q.leanGoal ρ
  | .all x p => ∀ n : Int, p.leanGoal (bind ρ x n)
  | .ex x p => ∃ n : Int, p.leanGoal (bind ρ x n)

theorem RichFormula.leanGoal_correct (ρ : Env) (p : RichFormula) :
    p.leanGoal ρ ↔ p.holds ρ := by
  induction p generalizing ρ <;>
    simp_all [leanGoal, holds, Formula.leanGoal_correct]

theorem pure_embedding (ρ : Env) (p : Formula) :
    (RichFormula.pure p).holds ρ ↔ p.holds ρ := Iff.rfl

/-- Frontend provenance is recorded without asserting coverage of either parser. -/
inductive Frontend where
  | acsl | cn
  deriving Repr, DecidableEq

structure SourceAssertion where
  frontend : Frontend
  body : RichFormula
  deriving Repr, DecidableEq

def SourceAssertion.holds (ρ : Env) (a : SourceAssertion) : Prop := a.body.holds ρ
def SourceAssertion.leanGoal (ρ : Env) (a : SourceAssertion) : Prop := a.body.leanGoal ρ

theorem SourceAssertion.leanGoal_correct (ρ : Env) (a : SourceAssertion) :
    a.leanGoal ρ ↔ a.holds ρ := a.body.leanGoal_correct ρ

/-- Changing frontend provenance preserves meaning in this shared fragment. -/
theorem frontend_agreement (ρ : Env) (p : RichFormula) :
    (SourceAssertion.mk .acsl p).holds ρ ↔ (SourceAssertion.mk .cn p).holds ρ := Iff.rfl

end Silmaril.Cerberus.Assertion.Pure
