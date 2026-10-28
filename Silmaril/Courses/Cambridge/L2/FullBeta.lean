module

public import Silmaril.Courses.Cambridge.L2.CallByName

/-! # Cambridge L2 full beta reduction, §4.2

The rules on p. 57 allow either side of an application to reduce, perform beta
substitution before the argument is a value, and reduce inside a lambda.
`BetaStep` extends the call-by-name rules with those contexts, propagating the
new reductions through the other L2 constructs as well.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2

inductive BetaStep : Config → Config → Prop where
  | name {before after : Config} (step : NameStep before after) :
      BetaStep before after
  | binaryLeft {left left' right : Expr} {op : Op} {s s' : Store}
      (inner : BetaStep ⟨left, s⟩ ⟨left', s'⟩) :
      BetaStep ⟨.binary left op right, s⟩ ⟨.binary left' op right, s'⟩
  | binaryRight {left right right' : Expr} {op : Op} {s s' : Store}
      (value : IsValue left) (inner : BetaStep ⟨right, s⟩ ⟨right', s'⟩) :
      BetaStep ⟨.binary left op right, s⟩ ⟨.binary left op right', s'⟩
  | assignStep {loc : Loc} {e e' : Expr} {s s' : Store}
      (inner : BetaStep ⟨e, s⟩ ⟨e', s'⟩) :
      BetaStep ⟨.assign loc e, s⟩ ⟨.assign loc e', s'⟩
  | seqStep {left left' right : Expr} {s s' : Store}
      (inner : BetaStep ⟨left, s⟩ ⟨left', s'⟩) :
      BetaStep ⟨.seq left right, s⟩ ⟨.seq left' right, s'⟩
  | ifStep {test test' yes no : Expr} {s s' : Store}
      (inner : BetaStep ⟨test, s⟩ ⟨test', s'⟩) :
      BetaStep ⟨.cond test yes no, s⟩ ⟨.cond test' yes no, s'⟩
  | appLeft {function function' argument : Expr} {s s' : Store}
      (inner : BetaStep ⟨function, s⟩ ⟨function', s'⟩) :
      BetaStep ⟨.app function argument, s⟩ ⟨.app function' argument, s'⟩
  | appRight {function argument argument' : Expr} {s s' : Store}
      (inner : BetaStep ⟨argument, s⟩ ⟨argument', s'⟩) :
      BetaStep ⟨.app function argument, s⟩ ⟨.app function argument', s'⟩
  | lamBody {domain : Ty} {body body' : Expr} {s s' : Store}
      (inner : BetaStep ⟨body, s⟩ ⟨body', s'⟩) :
      BetaStep ⟨.lam domain body, s⟩ ⟨.lam domain body', s'⟩
  | letStep {type : Ty} {value value' body : Expr} {s s' : Store}
      (inner : BetaStep ⟨value, s⟩ ⟨value', s'⟩) :
      BetaStep ⟨.letE type value body, s⟩ ⟨.letE type value' body, s'⟩

theorem nameStep_implies_beta {before after : Config}
    (step : NameStep before after) : BetaStep before after := .name step

theorem valueStep_implies_beta {before after : Config}
    (step : Step before after) : BetaStep before after := by
  induction step with
  | add left right s => exact .name (.add left right s)
  | ge left right s => exact .name (.ge left right s)
  | binaryLeft inner ih => exact .binaryLeft ih
  | binaryRight value inner ih => exact .binaryRight value ih
  | deref present => exact .name (.deref present)
  | assignValue present => exact .name (.assignValue present)
  | assignStep inner ih => exact .assignStep ih
  | seqSkip => exact .name .seqSkip
  | seqStep inner ih => exact .seqStep ih
  | ifTrue => exact .name .ifTrue
  | ifFalse => exact .name .ifFalse
  | ifStep inner ih => exact .ifStep ih
  | «while» => exact .name .while
  | appLeft inner ih => exact .appLeft ih
  | appRight value inner ih => exact .appRight ih
  | appFun value => exact .name .appFun
  | letStep inner ih => exact .letStep ih
  | letValue ready => exact .name (.letValue ready)
  | letRecFun => exact .name .letRecFun

abbrev BetaSteps : Config → Config → Prop := Relation.ReflTransGen BetaStep

theorem valueSteps_imply_beta {before after : Config}
    (steps : Steps before after) : BetaSteps before after :=
  (Relation.ReflTransGen.mono
    (fun _ _ step => valueStep_implies_beta step) before after) steps

theorem nameSteps_imply_beta {before after : Config}
    (steps : NameSteps before after) : BetaSteps before after :=
  (Relation.ReflTransGen.mono
    (fun _ _ step => nameStep_implies_beta step) before after) steps

/-- Full beta can reduce a lambda's body while call-by-value treats it as a value. -/
theorem reduces_inside_lambda (s : Store) :
    BetaStep
      ⟨.lam .int (.binary (.int 1) .add (.int 2)), s⟩
      ⟨.lam .int (.int 3), s⟩ := by
  exact .lamBody (.name (.add 1 2 s))

theorem value_cannot_reduce_inside_lambda (s : Store) :
    ¬ Step
      ⟨.lam .int (.binary (.int 1) .add (.int 2)), s⟩
      ⟨.lam .int (.int 3), s⟩ := by
  intro step
  exact value_terminal (.lam .int (.binary (.int 1) .add (.int 2))) _ step

end Silmaril.Courses.Cambridge.L2
