module

public import Silmaril.Courses.Cambridge.L2.CallByName
public import Silmaril.Courses.Cambridge.L2.Typing

/-! # Cambridge L2, Exercise 23

The outer function has type `unit → bool` and is applied to `skip`. Its body
applies a function that ignores its parameter to `l := 1`, then reads `l`.
Call by value runs the assignment first, producing `true`; call by name drops
the unused argument, producing `false` from the initial store `l ↦ 0`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Exercises.EvaluationStrategies

open Silmaril.Courses.Cambridge.L2

def Γ : TypeEnv :=
  { TypeEnv.empty with locs := (∅ : L1.TypeEnv).insert "l" .intref }

def initialStore : Store := L1.Store.fromList [("l", 0)]
def updatedStore : Store := initialStore.insert "l" 1

def readBool : Expr :=
  .cond (.binary (.deref "l") .ge (.int 1)) (.bool true) (.bool false)

def innerFunction : Expr := .lam .unit readBool
def innerCall : Expr := .app innerFunction (.assign "l" (.int 1))
def function : Expr := .lam .unit innerCall
def program : Expr := .app function .skip

theorem function_hasType : HasType Γ function (.arr .unit .bool) := by
  apply HasType.lam
  apply HasType.app
  · apply HasType.lam
    apply HasType.cond
    · exact HasType.ge (HasType.deref (by decide)) (HasType.int 1)
    · exact HasType.bool true
    · exact HasType.bool false
  · exact HasType.assign (by decide) (HasType.int 1)

theorem program_hasType : HasType Γ program .bool :=
  HasType.app function_hasType HasType.skip

def start : Config := ⟨program, initialStore⟩
def afterOuter : Config := ⟨innerCall, initialStore⟩

def valueAfterAssign : Config :=
  ⟨.app innerFunction .skip, updatedStore⟩
def valueAfterInner : Config := ⟨readBool, updatedStore⟩
def valueAfterRead : Config :=
  ⟨.cond (.binary (.int 1) .ge (.int 1)) (.bool true) (.bool false), updatedStore⟩
def valueAfterCompare : Config :=
  ⟨.cond (.bool true) (.bool true) (.bool false), updatedStore⟩
def valueResult : Config := ⟨.bool true, updatedStore⟩

theorem value_step1 : Step start afterOuter := by
  exact Step.appFun IsValue.skip

theorem value_step2 : Step afterOuter valueAfterAssign := by
  exact Step.appRight (IsValue.lam .unit readBool)
    (Step.assignValue (by decide))

theorem value_step3 : Step valueAfterAssign valueAfterInner := by
  exact Step.appFun IsValue.skip

theorem value_step4 : Step valueAfterInner valueAfterRead := by
  exact Step.ifStep (Step.binaryLeft (Step.deref (by decide)))

theorem value_step5 : Step valueAfterRead valueAfterCompare := by
  exact Step.ifStep (Step.ge 1 1 updatedStore)

theorem value_step6 : Step valueAfterCompare valueResult := Step.ifTrue

theorem value_trace :
    lts.MTr start [(), (), (), (), (), ()] valueResult :=
  .stepL value_step1
    (.stepL value_step2
      (.stepL value_step3
        (.stepL value_step4
          (.stepL value_step5 (.stepL value_step6 .refl)))))

theorem value_store : L1.Store.lookup valueResult.store "l" = some 1 := by
  decide

def nameAfterInner : Config := ⟨readBool, initialStore⟩
def nameAfterRead : Config :=
  ⟨.cond (.binary (.int 0) .ge (.int 1)) (.bool true) (.bool false), initialStore⟩
def nameAfterCompare : Config :=
  ⟨.cond (.bool false) (.bool true) (.bool false), initialStore⟩
def nameResult : Config := ⟨.bool false, initialStore⟩

theorem name_step1 : NameStep start afterOuter := NameStep.appFun
theorem name_step2 : NameStep afterOuter nameAfterInner := NameStep.appFun

theorem name_step3 : NameStep nameAfterInner nameAfterRead := by
  exact NameStep.ifStep (NameStep.binaryLeft (NameStep.deref (by decide)))

theorem name_step4 : NameStep nameAfterRead nameAfterCompare := by
  exact NameStep.ifStep (NameStep.ge 0 1 initialStore)

theorem name_step5 : NameStep nameAfterCompare nameResult := NameStep.ifFalse

theorem name_trace :
    nameLts.MTr start [(), (), (), (), ()] nameResult :=
  .stepL name_step1
    (.stepL name_step2
      (.stepL name_step3
        (.stepL name_step4 (.stepL name_step5 .refl))))

theorem name_store : L1.Store.lookup nameResult.store "l" = some 0 := by
  decide

end Silmaril.Courses.Cambridge.L2.Exercises.EvaluationStrategies
