module

public import Silmaril.Courses.Cambridge.L1.Exercises.OneToThree

/-! # Cambridge L1 exercises 4–5: two language-design variants

The rules on slides 53–54 replace operator order or assignment results. The
parameterized relation below spells out both alternatives, while `reduceWith`
adapts the appendix interpreter's pattern-matching strategy to each choice.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Exercises

inductive EvalOrder where
  | leftToRight
  | rightToLeft
  deriving DecidableEq, Repr

inductive AssignResult where
  | skip
  | integer
  deriving DecidableEq, Repr

inductive VariantStep (order : EvalOrder) (result : AssignResult) :
    Config → Config → Prop where
  | add (left right : Int) (s : Store) :
      VariantStep order result
        ⟨.binary (.int left) .add (.int right), s⟩ ⟨.int (left + right), s⟩
  | ge (left right : Int) (s : Store) :
      VariantStep order result
        ⟨.binary (.int left) .ge (.int right), s⟩ ⟨.bool (left ≥ right), s⟩
  | op1 {left left' right : Expr} {op : Op} {s s' : Store}
      (leftOrder : order = .leftToRight)
      (inner : VariantStep order result ⟨left, s⟩ ⟨left', s'⟩) :
      VariantStep order result
        ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | op2 {left right right' : Expr} {op : Op} {s s' : Store}
      (leftOrder : order = .leftToRight) (value : IsValue left)
      (inner : VariantStep order result ⟨right, s⟩ ⟨right', s'⟩) :
      VariantStep order result
        ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | op1b {left right right' : Expr} {op : Op} {s s' : Store}
      (rightOrder : order = .rightToLeft)
      (inner : VariantStep order result ⟨right, s⟩ ⟨right', s'⟩) :
      VariantStep order result
        ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | op2b {left left' right : Expr} {op : Op} {s s' : Store}
      (rightOrder : order = .rightToLeft) (value : IsValue right)
      (inner : VariantStep order result ⟨left, s⟩ ⟨left', s'⟩) :
      VariantStep order result
        ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | deref {loc : Loc} {s : Store} {n : Int} (present : Store.lookup s loc = some n) :
      VariantStep order result ⟨.deref loc, s⟩ ⟨.int n, s⟩
  | assign1 {loc : Loc} {s : Store} {n : Int}
      (skipResult : result = .skip) (present : loc ∈ s) :
      VariantStep order result ⟨.assign loc (.int n), s⟩ ⟨.skip, s.insert loc n⟩
  | assign1Prime {loc : Loc} {s : Store} {n : Int}
      (integerResult : result = .integer) (present : loc ∈ s) :
      VariantStep order result ⟨.assign loc (.int n), s⟩ ⟨.int n, s.insert loc n⟩
  | assign2 {loc : Loc} {e e' : Expr} {s s' : Store}
      (inner : VariantStep order result ⟨e, s⟩ ⟨e', s'⟩) :
      VariantStep order result ⟨.assign loc e, s⟩ ⟨.assign loc e', s'⟩
  | seq1 {e : Expr} {s : Store} (skipResult : result = .skip) :
      VariantStep order result ⟨.seq .skip e, s⟩ ⟨e, s⟩
  | seq1Prime {left right : Expr} {s : Store}
      (integerResult : result = .integer) (value : IsValue left) :
      VariantStep order result ⟨.seq left right, s⟩ ⟨right, s⟩
  | seq2 {left left' right : Expr} {s s' : Store}
      (inner : VariantStep order result ⟨left, s⟩ ⟨left', s'⟩) :
      VariantStep order result ⟨.seq left right, s⟩ ⟨.seq left' right, s'⟩
  | if1 {yes no : Expr} {s : Store} :
      VariantStep order result ⟨.cond (.bool true) yes no, s⟩ ⟨yes, s⟩
  | if2 {yes no : Expr} {s : Store} :
      VariantStep order result ⟨.cond (.bool false) yes no, s⟩ ⟨no, s⟩
  | if3 {test test' yes no : Expr} {s s' : Store}
      (inner : VariantStep order result ⟨test, s⟩ ⟨test', s'⟩) :
      VariantStep order result
        ⟨.cond test yes no, s⟩ ⟨.cond test' yes no, s'⟩
  | while {test body : Expr} {s : Store} :
      VariantStep order result ⟨.loop test body, s⟩
        ⟨.cond test (.seq body (.loop test body)) .skip, s⟩

abbrev RightStep := VariantStep .rightToLeft .skip
abbrev ValueAssignStep := VariantStep .leftToRight .integer

def variantLts (order : EvalOrder) (result : AssignResult) : Cslib.LTS Config Unit :=
  ⟨fun before _ after => VariantStep order result before after⟩

/-- The default policy contains every original L1 reduction. -/
theorem Step.toVariant {before after : Config} (step : Step before after) :
    VariantStep .leftToRight .skip before after := by
  induction step with
  | add left right s => exact .add left right s
  | ge left right s => exact .ge left right s
  | binaryLeft _ ih => exact .op1 rfl ih
  | binaryRight value _ ih => exact .op2 rfl value ih
  | deref present => exact .deref present
  | assignValue present => exact .assign1 rfl present
  | assignStep _ ih => exact .assign2 ih
  | seqSkip => exact .seq1 rfl
  | seqStep _ ih => exact .seq2 ih
  | ifTrue => exact .if1
  | ifFalse => exact .if2
  | ifStep _ ih => exact .if3 ih
  | «while» => exact .while

/-- The default policy adds no reductions to the printed L1 relation. -/
theorem VariantStep.toOriginal {before after : Config}
    (step : VariantStep .leftToRight .skip before after) : Step before after := by
  induction step with
  | add left right s => exact .add left right s
  | ge left right s => exact .ge left right s
  | op1 _ _ ih => exact .binaryLeft ih
  | op2 _ value _ ih => exact .binaryRight value ih
  | op1b impossible _ => cases impossible
  | op2b impossible _ _ => cases impossible
  | deref present => exact .deref present
  | assign1 _ present => exact .assignValue present
  | assign1Prime impossible _ => cases impossible
  | assign2 _ ih => exact .assignStep ih
  | seq1 _ => exact .seqSkip
  | seq1Prime impossible _ => cases impossible
  | seq2 _ ih => exact .seqStep ih
  | if1 => exact .ifTrue
  | if2 => exact .ifFalse
  | if3 _ ih => exact .ifStep ih
  | «while» => exact .while

theorem original_iff_default_variant {before after : Config} :
    Step before after ↔ VariantStep .leftToRight .skip before after :=
  ⟨Step.toVariant, VariantStep.toOriginal⟩

/-- An executable single-step interpreter for both exercise variants. -/
def reduceWith (order : EvalOrder) (result : AssignResult) (s : Store) :
    Expr → Option Config
  | .int _ | .bool _ | .skip => none
  | .binary left op right =>
      match left, op, right with
      | .int a, .add, .int b => some ⟨.int (a + b), s⟩
      | .int a, .ge, .int b => some ⟨.bool (a ≥ b), s⟩
      | _, _, _ =>
          match order with
          | .leftToRight =>
              if left.isValue then
                (reduceWith order result s right).map
                  (fun next => ⟨.binary left op next.expr, next.store⟩)
              else
                (reduceWith order result s left).map
                  (fun next => ⟨.binary next.expr op right, next.store⟩)
          | .rightToLeft =>
              if right.isValue then
                (reduceWith order result s left).map
                  (fun next => ⟨.binary next.expr op right, next.store⟩)
              else
                (reduceWith order result s right).map
                  (fun next => ⟨.binary left op next.expr, next.store⟩)
  | .cond test yes no =>
      match test with
      | .bool true => some ⟨yes, s⟩
      | .bool false => some ⟨no, s⟩
      | _ => (reduceWith order result s test).map
          (fun next => ⟨.cond next.expr yes no, next.store⟩)
  | .assign loc e =>
      match e with
      | .int n => (Store.update s loc n).map fun nextStore =>
          ⟨match result with
           | .skip => .skip
           | .integer => .int n, nextStore⟩
      | _ => (reduceWith order result s e).map
          (fun next => ⟨.assign loc next.expr, next.store⟩)
  | .deref loc => (Store.lookup s loc).map fun n => ⟨.int n, s⟩
  | .seq left right =>
      match result, left with
      | .skip, .skip => some ⟨right, s⟩
      | .integer, left =>
          if left.isValue then some ⟨right, s⟩
          else (reduceWith order result s left).map
            (fun next => ⟨.seq next.expr right, next.store⟩)
      | .skip, left => (reduceWith order result s left).map
          (fun next => ⟨.seq next.expr right, next.store⟩)
  | .loop test body => some ⟨.cond test (.seq body (.loop test body)) .skip, s⟩

def reduceConfig (order : EvalOrder) (result : AssignResult) (c : Config) :
    Option Config := reduceWith order result c.store c.expr

/-- Run exactly as far as the given fuel allows, stopping early on no step. -/
def run (order : EvalOrder) (result : AssignResult) : Nat → Config → Config
  | 0, c => c
  | fuel + 1, c =>
      match reduceConfig order result c with
      | none => c
      | some next => run order result fuel next

/-! ## Distinguishing programs from slides 53–54 -/

def orderStore : Store := Store.fromList [("l", 0)]
def leftEffect : Expr := .seq (.assign "l" (.int 1)) (.int 0)
def rightEffect : Expr := .seq (.assign "l" (.int 2)) (.int 0)
def orderStart : Config := ⟨.binary leftEffect .add rightEffect, orderStore⟩

def leftAfter1 : Config :=
  ⟨.binary (.seq .skip (.int 0)) .add rightEffect, orderStore.insert "l" 1⟩
def leftAfter2 : Config :=
  ⟨.binary (.int 0) .add rightEffect, leftAfter1.store⟩
def leftAfter3 : Config :=
  ⟨.binary (.int 0) .add (.seq .skip (.int 0)), leftAfter2.store.insert "l" 2⟩
def leftAfter4 : Config :=
  ⟨.binary (.int 0) .add (.int 0), leftAfter3.store⟩
def leftResult : Config := ⟨.int 0, leftAfter4.store⟩

theorem left_step1 : VariantStep .leftToRight .skip orderStart leftAfter1 :=
  .op1 rfl (.seq2 (.assign1 rfl (by decide)))

theorem left_step2 : VariantStep .leftToRight .skip leftAfter1 leftAfter2 :=
  .op1 rfl (.seq1 rfl)

theorem left_step3 : VariantStep .leftToRight .skip leftAfter2 leftAfter3 :=
  .op2 rfl (.int 0) (.seq2 (.assign1 rfl (by decide)))

theorem left_step4 : VariantStep .leftToRight .skip leftAfter3 leftAfter4 :=
  .op2 rfl (.int 0) (.seq1 rfl)

theorem left_step5 : VariantStep .leftToRight .skip leftAfter4 leftResult :=
  .add 0 0 leftAfter4.store

theorem left_trace :
    (variantLts .leftToRight .skip).MTr orderStart [(), (), (), (), ()] leftResult :=
  .stepL left_step1 (.stepL left_step2
    (.stepL left_step3 (.stepL left_step4 (.stepL left_step5 .refl))))

def rightAfter1 : Config :=
  ⟨.binary leftEffect .add (.seq .skip (.int 0)), orderStore.insert "l" 2⟩
def rightAfter2 : Config :=
  ⟨.binary leftEffect .add (.int 0), rightAfter1.store⟩
def rightAfter3 : Config :=
  ⟨.binary (.seq .skip (.int 0)) .add (.int 0), rightAfter2.store.insert "l" 1⟩
def rightAfter4 : Config :=
  ⟨.binary (.int 0) .add (.int 0), rightAfter3.store⟩
def rightResult : Config := ⟨.int 0, rightAfter4.store⟩

theorem right_step1 : RightStep orderStart rightAfter1 :=
  .op1b rfl (.seq2 (.assign1 rfl (by decide)))

theorem right_step2 : RightStep rightAfter1 rightAfter2 :=
  .op1b rfl (.seq1 rfl)

theorem right_step3 : RightStep rightAfter2 rightAfter3 :=
  .op2b rfl (.int 0) (.seq2 (.assign1 rfl (by decide)))

theorem right_step4 : RightStep rightAfter3 rightAfter4 :=
  .op2b rfl (.int 0) (.seq1 rfl)

theorem right_step5 : RightStep rightAfter4 rightResult :=
  .add 0 0 rightAfter4.store

theorem right_trace :
    (variantLts .rightToLeft .skip).MTr orderStart [(), (), (), (), ()] rightResult :=
  .stepL right_step1 (.stepL right_step2
    (.stepL right_step3 (.stepL right_step4 (.stepL right_step5 .refl))))

theorem left_result_store : Store.lookup leftResult.store "l" = some 2 := by
  simp [leftResult, leftAfter4, leftAfter3]

theorem right_result_store : Store.lookup rightResult.store "l" = some 1 := by
  simp [rightResult, rightAfter4, rightAfter3]

theorem left_order_result :
    run .leftToRight .skip 5 orderStart =
      ⟨.int 0, orderStore.insert "l" 2⟩ := by decide

theorem right_order_result :
    run .rightToLeft .skip 5 orderStart =
      ⟨.int 0, orderStore.insert "l" 1⟩ := by decide

def resultStart : Config := ⟨.assign "l" (.int 1), orderStore⟩

theorem original_assignment_result :
    reduceConfig .leftToRight .skip resultStart =
      some ⟨.skip, orderStore.insert "l" 1⟩ := by decide

theorem integer_assignment_result :
    reduceConfig .leftToRight .integer resultStart =
      some ⟨.int 1, orderStore.insert "l" 1⟩ := by decide

theorem integer_assignment_step :
    ValueAssignStep resultStart ⟨.int 1, orderStore.insert "l" 1⟩ :=
  .assign1Prime rfl (by decide)

theorem integer_sequence_result :
    reduceConfig .leftToRight .integer ⟨.seq (.int 1) (.int 2), orderStore⟩ =
      some ⟨.int 2, orderStore⟩ := by decide

theorem integer_sequence_step :
    ValueAssignStep ⟨.seq (.int 1) (.int 2), orderStore⟩
      ⟨.int 2, orderStore⟩ :=
  .seq1Prime rfl (.int 1)

/-- An assignment used as an operand exposes the changed result type. -/
def assignmentOperand : Config :=
  ⟨.binary (.assign "l" (.int 1)) .add (.int 2), orderStore⟩

theorem original_assignment_operand :
    run .leftToRight .skip 3 assignmentOperand =
      ⟨.binary .skip .add (.int 2), orderStore.insert "l" 1⟩ := by decide

theorem integer_assignment_operand :
    run .leftToRight .integer 3 assignmentOperand =
      ⟨.int 3, orderStore.insert "l" 1⟩ := by decide

theorem original_integer_sequence_stuck :
    reduceConfig .leftToRight .skip ⟨.seq (.int 1) (.int 2), orderStore⟩ = none :=
  rfl

end Silmaril.Courses.Cambridge.L1.Exercises
