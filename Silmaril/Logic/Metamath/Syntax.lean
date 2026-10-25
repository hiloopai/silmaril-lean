module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-!
# Metamath syntax

Metamath's semantics is string rewriting. A math string is a list of symbols;
each symbol is a constant or a variable. An expression begins with a constant,
its typecode (`wff`, `class`, `|-`, ...), followed by an arbitrary string.

An assertion is Metamath's "extended frame": its disjoint-variable pairs, its
mandatory hypotheses in database order, and its conclusion. Floating
hypotheses `t v` assign typecode `t` to variable `v`; essential hypotheses are
arbitrary expressions. Constants and variables are generic types here. The
text format instantiates both with strings (`Silmaril.Logic.Metamath.Text`).

Substitution replaces every variable by a string and leaves constants alone.
This is exactly the substitution performed by a Metamath proof step.
-/

namespace Silmaril.Logic.Metamath

universe u

/-- A math symbol: a constant or a variable. -/
inductive Sym (C V : Type u) where
  | const (c : C)
  | var (v : V)
  deriving DecidableEq, Repr, Hashable

/-- A math string. -/
abbrev Str (C V : Type u) := List (Sym C V)

/-- An expression: a typecode followed by a math string. -/
structure Expr (C V : Type u) where
  tc : C
  body : Str C V
  deriving DecidableEq, Repr, Hashable

/-- A mandatory hypothesis of an assertion. -/
inductive Hyp (C V : Type u) where
  /-- The floating hypothesis `tc v`. -/
  | float (tc : C) (v : V)
  /-- An essential hypothesis. -/
  | ess (e : Expr C V)
  deriving DecidableEq, Repr, Hashable

/-- An assertion (extended frame): disjoint-variable pairs, mandatory hypotheses
in database order, and a conclusion. -/
structure Assertion (C V : Type u) where
  dv : List (V × V)
  hyps : List (Hyp C V)
  concl : Expr C V
  deriving DecidableEq, Repr, Hashable

/-- A substitution assigns a math string to each variable. -/
abbrev Subst (C V : Type u) := V → Str C V

variable {C V : Type u}

namespace Sym

/-- The variables of a symbol, as a list. -/
def vars : Sym C V → List V
  | const _ => []
  | var v => [v]

/-- Substitution into a single symbol. -/
def subst (s : Subst C V) : Sym C V → Str C V
  | const c => [const c]
  | var v => s v

@[simp] theorem subst_const (s : Subst C V) (c : C) : (const c : Sym C V).subst s = [const c] :=
  rfl

@[simp] theorem subst_var (s : Subst C V) (v : V) : (var v : Sym C V).subst s = s v := rfl

@[simp] theorem vars_const (c : C) : (const c : Sym C V).vars = [] := rfl

@[simp] theorem vars_var (v : V) : (var v : Sym C V).vars = [v] := rfl

end Sym

namespace Str

/-- The variables occurring in a string, with multiplicity and in order. -/
def vars (s : Str C V) : List V := s.flatMap Sym.vars

/-- Simultaneous substitution into a string. -/
def subst (σ : Subst C V) (s : Str C V) : Str C V := s.flatMap (Sym.subst σ)

@[simp] theorem vars_nil : vars ([] : Str C V) = [] := rfl

@[simp] theorem vars_cons (a : Sym C V) (s : Str C V) : vars (a :: s) = a.vars ++ vars s := by
  simp [vars]

@[simp] theorem vars_append (s t : Str C V) : vars (s ++ t) = vars s ++ vars t := by
  simp [vars]

@[simp] theorem subst_nil (σ : Subst C V) : subst σ ([] : Str C V) = [] := rfl

@[simp] theorem subst_cons (σ : Subst C V) (a : Sym C V) (s : Str C V) :
    subst σ (a :: s) = a.subst σ ++ subst σ s := by
  simp [subst]

@[simp] theorem subst_append (σ : Subst C V) (s t : Str C V) :
    subst σ (s ++ t) = subst σ s ++ subst σ t := by
  simp [subst]

theorem mem_vars {s : Str C V} {v : V} : v ∈ vars s ↔ Sym.var v ∈ s := by
  induction s with
  | nil => simp
  | cons a s ih =>
    cases a <;> simp [ih, eq_comm]

/-- The identity substitution. -/
@[simp] theorem subst_var (s : Str C V) : subst (fun v => [Sym.var v]) s = s := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [ih]

/-- Substitution composes. -/
theorem subst_subst (σ τ : Subst C V) (s : Str C V) :
    subst τ (subst σ s) = subst (fun v => subst τ (σ v)) s := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [ih]

/-- Substitution only depends on the variables that occur. -/
theorem subst_congr {σ τ : Subst C V} {s : Str C V} (h : ∀ v ∈ vars s, σ v = τ v) :
    subst σ s = subst τ s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases a with
    | const c => simp [ih (fun v hv => h v (by simp [hv]))]
    | var v =>
      simp only [subst_cons, Sym.subst_var]
      rw [h v (by simp), ih (fun w hw => h w (by simp [hw]))]

/-- The variables of a substituted string. -/
theorem mem_vars_subst {σ : Subst C V} {s : Str C V} {w : V} :
    w ∈ vars (subst σ s) ↔ ∃ v ∈ vars s, w ∈ vars (σ v) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    cases a with
    | const c => simp [ih]
    | var v => simp [ih, or_and_right, exists_or]

end Str

namespace Expr

/-- The variables of an expression. -/
def vars (e : Expr C V) : List V := Str.vars e.body

/-- Substitution into an expression preserves its typecode. -/
def subst (σ : Subst C V) (e : Expr C V) : Expr C V := ⟨e.tc, Str.subst σ e.body⟩

/-- The expression as a flat math string, typecode first. -/
def toStr (e : Expr C V) : Str C V := Sym.const e.tc :: e.body

@[simp] theorem subst_tc (σ : Subst C V) (e : Expr C V) : (e.subst σ).tc = e.tc := rfl

@[simp] theorem subst_body (σ : Subst C V) (e : Expr C V) :
    (e.subst σ).body = Str.subst σ e.body := rfl

@[simp] theorem subst_var (e : Expr C V) : e.subst (fun v => [Sym.var v]) = e := by
  cases e; simp [subst]

theorem subst_subst (σ τ : Subst C V) (e : Expr C V) :
    (e.subst σ).subst τ = e.subst (fun v => Str.subst τ (σ v)) := by
  cases e; simp [subst, Str.subst_subst]

theorem subst_congr {σ τ : Subst C V} {e : Expr C V} (h : ∀ v ∈ e.vars, σ v = τ v) :
    e.subst σ = e.subst τ := by
  cases e; simp only [subst, Expr.mk.injEq, true_and]; exact Str.subst_congr h

end Expr

namespace Hyp

/-- The expression a hypothesis asserts. -/
def expr : Hyp C V → Expr C V
  | float tc v => ⟨tc, [Sym.var v]⟩
  | ess e => e

/-- The variables of a hypothesis. -/
def vars (h : Hyp C V) : List V := h.expr.vars

@[simp] theorem expr_float (tc : C) (v : V) : (float tc v).expr = ⟨tc, [Sym.var v]⟩ := rfl

@[simp] theorem expr_ess (e : Expr C V) : (ess e : Hyp C V).expr = e := rfl

end Hyp

namespace Assertion

/-- The hypothesis expressions, in order. -/
def hypExprs (A : Assertion C V) : List (Expr C V) := A.hyps.map Hyp.expr

/-- The floating hypotheses `(typecode, variable)`, in order. -/
def floats (A : Assertion C V) : List (C × V) :=
  A.hyps.filterMap fun
    | .float tc v => some (tc, v)
    | .ess _ => none

/-- The essential hypotheses, in order. -/
def essentials (A : Assertion C V) : List (Expr C V) :=
  A.hyps.filterMap fun
    | .float _ _ => none
    | .ess e => some e

/-- The variables occurring in the essential hypotheses or the conclusion. -/
def vars (A : Assertion C V) : List V :=
  A.concl.vars ++ A.essentials.flatMap Expr.vars

/-- The symmetric disjointness relation declared by the assertion. -/
def Disjoint (A : Assertion C V) (x y : V) : Prop := (x, y) ∈ A.dv ∨ (y, x) ∈ A.dv

instance [DecidableEq V] (A : Assertion C V) (x y : V) : Decidable (A.Disjoint x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem Disjoint.symm {A : Assertion C V} {x y : V} (h : A.Disjoint x y) : A.Disjoint y x :=
  Or.symm h

/-- Apply a substitution to every hypothesis and the conclusion. -/
def substExprs (A : Assertion C V) (σ : Subst C V) : List (Expr C V) :=
  A.hypExprs.map (Expr.subst σ)

/-- `σ` respects `A`'s disjoint-variable conditions inside a context whose
disjointness relation is `disj`: substituted strings for a declared disjoint
pair share no variable, and every pair of their variables is disjoint in the
context. This is Metamath's `$d` check. -/
def DVSafe (A : Assertion C V) (σ : Subst C V) (disj : V → V → Prop) : Prop :=
  ∀ x y, (x, y) ∈ A.dv →
    ∀ a ∈ Str.vars (σ x), ∀ b ∈ Str.vars (σ y), a ≠ b ∧ disj a b

/-- Well-formedness required of every axiom and theorem: all variables have a
floating hypothesis, floating hypotheses name distinct variables, and declared
disjoint pairs are distinct variables. -/
structure WellFormed (A : Assertion C V) : Prop where
  vars_float : ∀ v ∈ A.vars, ∃ tc, Hyp.float tc v ∈ A.hyps
  floats_nodup : (A.floats.map Prod.snd).Nodup
  dv_irrefl : ∀ x y, (x, y) ∈ A.dv → x ≠ y

end Assertion

end Silmaril.Logic.Metamath
