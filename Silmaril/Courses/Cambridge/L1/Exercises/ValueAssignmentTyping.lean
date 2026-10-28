module

public import Silmaril.Courses.Cambridge.L1.Exercises.TypingDerivations

/-! # Cambridge L1 Exercises 9–10: typing integer-returning assignment

With `(assign1')`, assignment reduces to an integer, so it must itself have
type `int`. With `(seq1')`, every value can be discarded by sequencing, so the
first expression may have any type. The second expression determines the
sequence's result type. These are the only changed typing rules.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Exercises

/-! ## Exercise 9: the old assignment type is not preserved -/

def resultTypeEnv : TypeEnv := (∅ : TypeEnv).insert "l" .intref

theorem old_assignment_typed : HasType resultTypeEnv resultStart.expr .unit :=
  .assign (by decide) (.int 1)

theorem old_assignment_reduces :
    ValueAssignStep resultStart ⟨.int 1, orderStore.insert "l" 1⟩ :=
  integer_assignment_step

theorem old_assignment_result_not_unit :
    ¬ HasType resultTypeEnv (.int 1) .unit := by
  intro typing
  cases typing

/-! ## Revised typing rules -/

inductive ValueHasType (Γ : TypeEnv) : Expr → Ty → Prop where
  | int (n : Int) : ValueHasType Γ (.int n) .int
  | bool (b : Bool) : ValueHasType Γ (.bool b) .bool
  | add {left right : Expr}
      (hl : ValueHasType Γ left .int) (hr : ValueHasType Γ right .int) :
      ValueHasType Γ (.binary left .add right) .int
  | ge {left right : Expr}
      (hl : ValueHasType Γ left .int) (hr : ValueHasType Γ right .int) :
      ValueHasType Γ (.binary left .ge right) .bool
  | cond {test yes no : Expr} {T : Ty}
      (hc : ValueHasType Γ test .bool)
      (hy : ValueHasType Γ yes T) (hn : ValueHasType Γ no T) :
      ValueHasType Γ (.cond test yes no) T
  | assign {loc : Loc} {e : Expr}
      (present : loc ∈ Γ) (he : ValueHasType Γ e .int) :
      ValueHasType Γ (.assign loc e) .int
  | deref {loc : Loc} (present : loc ∈ Γ) :
      ValueHasType Γ (.deref loc) .int
  | skip : ValueHasType Γ .skip .unit
  | seq {left right : Expr} {L T : Ty}
      (hl : ValueHasType Γ left L) (hr : ValueHasType Γ right T) :
      ValueHasType Γ (.seq left right) T
  | loop {test body : Expr} {B : Ty}
      (ht : ValueHasType Γ test .bool) (hb : ValueHasType Γ body B) :
      ValueHasType Γ (.loop test body) .unit

/-- The revised inference algorithm for Exercise 10. -/
def inferValue (Γ : TypeEnv) : Expr → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .binary left .add right =>
      if inferValue Γ left = some .int ∧ inferValue Γ right = some .int then
        some .int else none
  | .binary left .ge right =>
      if inferValue Γ left = some .int ∧ inferValue Γ right = some .int then
        some .bool else none
  | .cond test yes no =>
      match inferValue Γ test, inferValue Γ yes, inferValue Γ no with
      | some .bool, some tyYes, some tyNo =>
          if tyYes = tyNo then some tyYes else none
      | _, _, _ => none
  | .assign loc e =>
      if loc ∈ Γ ∧ inferValue Γ e = some .int then some .int else none
  | .deref loc => if loc ∈ Γ then some .int else none
  | .skip => some .unit
  | .seq left right =>
      if (inferValue Γ left).isSome then inferValue Γ right else none
  | .loop test body =>
      if inferValue Γ test = some .bool ∧ (inferValue Γ body).isSome then
        some .unit else none

theorem inferValue_complete {Γ : TypeEnv} {e : Expr} {T : Ty}
    (typing : ValueHasType Γ e T) : inferValue Γ e = some T := by
  induction typing <;> simp_all [inferValue]

theorem inferValue_sound {Γ : TypeEnv} :
    ∀ e T, inferValue Γ e = some T → ValueHasType Γ e T := by
  intro e
  induction e with
  | int n =>
      intro T h
      cases h
      exact .int n
  | bool b =>
      intro T h
      cases h
      exact .bool b
  | binary left op right ihLeft ihRight =>
      intro T h
      cases op with
      | add =>
          simp only [inferValue] at h
          split_ifs at h with valid
          · cases h
            exact .add (ihLeft .int valid.1) (ihRight .int valid.2)
      | ge =>
          simp only [inferValue] at h
          split_ifs at h with valid
          · cases h
            exact .ge (ihLeft .int valid.1) (ihRight .int valid.2)
  | cond test yes no ihTest ihYes ihNo =>
      intro T h
      simp only [inferValue] at h
      split at h <;> try cases h
      split_ifs at h with same
      · cases h
        exact .cond (ihTest .bool (by assumption))
          (ihYes _ (by assumption)) (ihNo _ (by simpa [same] using ‹_›))
  | assign loc e ih =>
      intro T h
      simp only [inferValue] at h
      split_ifs at h with valid
      · cases h
        exact .assign valid.1 (ih .int valid.2)
  | deref loc =>
      intro T h
      simp only [inferValue] at h
      split_ifs at h with present
      · cases h
        exact .deref present
  | skip =>
      intro T h
      cases h
      exact .skip
  | seq left right ihLeft ihRight =>
      intro T h
      simp only [inferValue] at h
      split_ifs at h with leftType
      · cases result : inferValue Γ left with
        | none => simp [result] at leftType
        | some L => exact .seq (ihLeft L result) (ihRight T h)
  | loop test body ihTest ihBody =>
      intro T h
      simp only [inferValue] at h
      split_ifs at h with valid
      · cases h
        cases result : inferValue Γ body with
        | none => simp [result] at valid
        | some B => exact .loop (ihTest .bool valid.1) (ihBody B result)

theorem inferValue_iff_hasType {Γ : TypeEnv} {e : Expr} {T : Ty} :
    inferValue Γ e = some T ↔ ValueHasType Γ e T :=
  ⟨inferValue_sound e T, inferValue_complete⟩

theorem ValueHasType.unique {Γ : TypeEnv} {e : Expr} {T U : Ty}
    (first : ValueHasType Γ e T) (second : ValueHasType Γ e U) : T = U := by
  have firstResult := inferValue_complete first
  have secondResult := inferValue_complete second
  simpa [firstResult] using secondResult

instance (Γ : TypeEnv) (e : Expr) (T : Ty) : Decidable (ValueHasType Γ e T) :=
  decidable_of_iff (inferValue Γ e = some T) inferValue_iff_hasType

theorem value_assignment_typed :
    ValueHasType resultTypeEnv resultStart.expr .int :=
  .assign (by decide) (.int 1)

theorem value_sequence_typed :
    ValueHasType assignmentTypeEnv (.seq (.int 1) (.int 2)) .int :=
  .seq (.int 1) (.int 2)

theorem revised_inference_examples :
    inferValue resultTypeEnv resultStart.expr = some .int ∧
    inferValue assignmentTypeEnv (.seq (.int 1) (.int 2)) = some .int := by
  decide

/-- The revised rules restore type preservation for every variant step. -/
theorem value_assignment_preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (typed : ValueHasType Γ before.expr T)
    (step : ValueAssignStep before after) : ValueHasType Γ after.expr T := by
  induction step generalizing T with
  | add left right s =>
      cases typed
      exact .int (left + right)
  | ge left right s =>
      cases typed
      exact .bool (left ≥ right)
  | op1 _ inner ih =>
      cases typed with
      | add hl hr => exact .add (ih hl) hr
      | ge hl hr => exact .ge (ih hl) hr
  | op2 _ _ inner ih =>
      cases typed with
      | add hl hr => exact .add hl (ih hr)
      | ge hl hr => exact .ge hl (ih hr)
  | op1b impossible _ => cases impossible
  | op2b impossible _ _ => cases impossible
  | deref _ =>
      cases typed
      exact .int _
  | assign1 impossible _ => cases impossible
  | assign1Prime _ _ =>
      cases typed
      exact .int _
  | assign2 inner ih =>
      cases typed with
      | assign present he => exact .assign present (ih he)
  | seq1 impossible => cases impossible
  | seq1Prime _ _ =>
      cases typed with
      | seq _ hr => exact hr
  | seq2 inner ih =>
      cases typed with
      | seq hl hr => exact .seq (ih hl) hr
  | if1 =>
      cases typed with
      | cond _ hy _ => exact hy
  | if2 =>
      cases typed with
      | cond _ _ hn => exact hn
  | if3 inner ih =>
      cases typed with
      | cond hc hy hn => exact .cond (ih hc) hy hn
  | «while» =>
      cases typed with
      | loop ht hb => exact .cond ht (.seq hb (.loop ht hb)) .skip

end Silmaril.Courses.Cambridge.L1.Exercises
