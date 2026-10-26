module

public import Silmaril.Courses.Cambridge.L2.Metatheory.Closedness

/-! # Cambridge L2 progress, Theorem 18

A closed, well-typed expression is a value or can reduce when the store covers
the location assumptions. The closedness premise rules out free variables and
dangling de Bruijn indices. Canonical forms rule out applications of non-lambda
values and primitive operations on values of the wrong type.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

theorem typed_integer_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .int) (value : IsValue e) : ∃ n, e = .int n := by
  cases value with
  | int n => exact ⟨n, rfl⟩
  | bool => cases typing
  | skip => cases typing
  | lam => cases typing

theorem typed_boolean_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .bool) (value : IsValue e) : ∃ b, e = .bool b := by
  cases value with
  | int => cases typing
  | bool b => exact ⟨b, rfl⟩
  | skip => cases typing
  | lam => cases typing

theorem typed_unit_value {Γ : TypeEnv} {e : Expr}
    (typing : HasType Γ e .unit) (value : IsValue e) : e = .skip := by
  cases value with
  | int => cases typing
  | bool => cases typing
  | skip => rfl
  | lam => cases typing

theorem typed_function_value {Γ : TypeEnv} {e : Expr} {domain codomain : Ty}
    (typing : HasType Γ e (.arr domain codomain)) (value : IsValue e) :
    ∃ body, e = .lam domain body := by
  cases value with
  | int => cases typing
  | bool => cases typing
  | skip => cases typing
  | lam parameter body =>
      cases typing
      exact ⟨body, rfl⟩

theorem Expr.Closed.binary_left {left right : Expr} {op : Op}
    (closed : (Expr.binary left op right).Closed) : left.Closed :=
  ⟨closed.1.1, (Finset.union_eq_empty.mp closed.2).1⟩

theorem Expr.Closed.binary_right {left right : Expr} {op : Op}
    (closed : (Expr.binary left op right).Closed) : right.Closed :=
  ⟨closed.1.2, (Finset.union_eq_empty.mp closed.2).2⟩

theorem Expr.Closed.cond_test {test yes no : Expr}
    (closed : (Expr.cond test yes no).Closed) : test.Closed :=
  ⟨closed.1.1, (Finset.union_eq_empty.mp
    (Finset.union_eq_empty.mp closed.2).1).1⟩

theorem Expr.Closed.assign_value {loc : Loc} {value : Expr}
    (closed : (Expr.assign loc value).Closed) : value.Closed := closed

theorem Expr.Closed.seq_left {left right : Expr}
    (closed : (Expr.seq left right).Closed) : left.Closed :=
  ⟨closed.1.1, (Finset.union_eq_empty.mp closed.2).1⟩

theorem Expr.Closed.app_function {function argument : Expr}
    (closed : (Expr.app function argument).Closed) : function.Closed :=
  ⟨closed.1.1, (Finset.union_eq_empty.mp closed.2).1⟩

theorem Expr.Closed.app_argument {function argument : Expr}
    (closed : (Expr.app function argument).Closed) : argument.Closed :=
  ⟨closed.1.2, (Finset.union_eq_empty.mp closed.2).2⟩

theorem Expr.Closed.let_value {type : Ty} {value body : Expr}
    (closed : (Expr.letE type value body).Closed) : value.Closed :=
  ⟨closed.1.1, (Finset.union_eq_empty.mp closed.2).1⟩

/-- Theorem 18, with the notes' closedness and allocated-location hypotheses. -/
theorem progress {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typing : HasType Γ e T) (closed : e.Closed)
    (covers : StoreCovers Γ s) :
    IsValue e ∨ ∃ after, Step ⟨e, s⟩ after := by
  induction typing generalizing s with
  | int n => exact Or.inl (.int n)
  | bool b => exact Or.inl (.bool b)
  | add hl hr ihLeft ihRight =>
      rcases ihLeft closed.binary_left covers with valueLeft | ⟨next, stepLeft⟩
      · rcases ihRight closed.binary_right covers with valueRight | ⟨next, stepRight⟩
        · obtain ⟨a, rfl⟩ := typed_integer_value hl valueLeft
          obtain ⟨b, rfl⟩ := typed_integer_value hr valueRight
          exact Or.inr ⟨⟨.int (a + b), s⟩, .add a b s⟩
        · exact Or.inr ⟨⟨.binary _ .add next.expr, next.store⟩,
            .binaryRight valueLeft stepRight⟩
      · exact Or.inr ⟨⟨.binary next.expr .add _, next.store⟩,
          .binaryLeft stepLeft⟩
  | ge hl hr ihLeft ihRight =>
      rcases ihLeft closed.binary_left covers with valueLeft | ⟨next, stepLeft⟩
      · rcases ihRight closed.binary_right covers with valueRight | ⟨next, stepRight⟩
        · obtain ⟨a, rfl⟩ := typed_integer_value hl valueLeft
          obtain ⟨b, rfl⟩ := typed_integer_value hr valueRight
          exact Or.inr ⟨⟨.bool (a ≥ b), s⟩, .ge a b s⟩
        · exact Or.inr ⟨⟨.binary _ .ge next.expr, next.store⟩,
            .binaryRight valueLeft stepRight⟩
      · exact Or.inr ⟨⟨.binary next.expr .ge _, next.store⟩,
          .binaryLeft stepLeft⟩
  | cond hc hy hn ihTest _ _ =>
      rcases ihTest closed.cond_test covers with valueTest | ⟨next, stepTest⟩
      · obtain ⟨b, rfl⟩ := typed_boolean_value hc valueTest
        cases b
        · exact Or.inr ⟨⟨_, s⟩, .ifFalse⟩
        · exact Or.inr ⟨⟨_, s⟩, .ifTrue⟩
      · exact Or.inr ⟨⟨.cond next.expr _ _, next.store⟩, .ifStep stepTest⟩
  | assign present he ih =>
      rcases ih closed.assign_value covers with value | ⟨next, step⟩
      · obtain ⟨n, rfl⟩ := typed_integer_value he value
        exact Or.inr ⟨⟨.skip, s.insert _ n⟩, .assignValue (covers _ present)⟩
      · exact Or.inr ⟨⟨.assign _ next.expr, next.store⟩, .assignStep step⟩
  | deref present =>
      obtain ⟨n, found⟩ := Finmap.mem_iff.mp (covers _ present)
      exact Or.inr ⟨⟨.int n, s⟩, .deref found⟩
  | skip => exact Or.inl .skip
  | seq hl hr ihLeft _ =>
      rcases ihLeft closed.seq_left covers with valueLeft | ⟨next, stepLeft⟩
      · have skip := typed_unit_value hl valueLeft
        subst_vars
        exact Or.inr ⟨⟨_, s⟩, .seqSkip⟩
      · exact Or.inr ⟨⟨.seq next.expr _, next.store⟩, .seqStep stepLeft⟩
  | loop => exact Or.inr ⟨⟨_, s⟩, .while⟩
  | bvar lookup =>
      exact False.elim (Nat.not_lt_zero _ closed.1)
  | fvar lookup =>
      simp [Expr.Closed, Expr.freeVars] at closed
  | lam => exact Or.inl (.lam _ _)
  | app hf ha ihFunction ihArgument =>
      rcases ihFunction closed.app_function covers with
        valueFunction | ⟨next, stepFunction⟩
      · rcases ihArgument closed.app_argument covers with
          valueArgument | ⟨next, stepArgument⟩
        · obtain ⟨body, rfl⟩ := typed_function_value hf valueFunction
          exact Or.inr ⟨⟨body.beta _, s⟩, .appFun valueArgument⟩
        · exact Or.inr ⟨⟨.app _ next.expr, next.store⟩,
            .appRight valueFunction stepArgument⟩
      · exact Or.inr ⟨⟨.app next.expr _, next.store⟩,
          .appLeft stepFunction⟩
  | letE hv hb ihValue _ =>
      rcases ihValue closed.let_value covers with value | ⟨next, step⟩
      · exact Or.inr ⟨⟨_, s⟩, .letValue value⟩
      · exact Or.inr ⟨⟨.letE _ next.expr _, next.store⟩, .letStep step⟩
  | letRecFun => exact Or.inr ⟨⟨_, s⟩, .letRecFun⟩

theorem not_stuck {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typing : HasType Γ e T) (closed : e.Closed)
    (covers : StoreCovers Γ s) :
    ¬ Stuck ⟨e, s⟩ := by
  intro ⟨notValue, terminal⟩
  rcases progress typing closed covers with value | ⟨next, step⟩
  · exact notValue value
  · exact terminal next step

end Silmaril.Courses.Cambridge.L2
