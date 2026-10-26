module

public import Silmaril.Courses.Cambridge.L1.Exercises.ValueAssignmentTyping

/-! # Cambridge L1 Exercise 11: operator and sequence order

The printed L1 semantics and appendix interpreter both reduce the left
operator argument first, and finish the left side of a sequence before its
right side. The existing Exercise 4 traces show how reversing operator order
changes an observable store value. The sequence trace below checks the other
half of the question in the original reduction relation.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.Exercises

theorem original_operator_order_trace :
    lts.MTr orderStart [(), (), (), (), ()] leftResult :=
  .stepL (VariantStep.toOriginal left_step1)
    (.stepL (VariantStep.toOriginal left_step2)
      (.stepL (VariantStep.toOriginal left_step3)
        (.stepL (VariantStep.toOriginal left_step4)
          (.stepL (VariantStep.toOriginal left_step5) .refl))))

def sequenceStart : Config :=
  ⟨.seq (.assign "l" (.int 1)) (.assign "l" (.int 2)), orderStore⟩

def sequenceAfter1 : Config :=
  ⟨.seq .skip (.assign "l" (.int 2)), orderStore.insert "l" 1⟩

def sequenceAfter2 : Config :=
  ⟨.assign "l" (.int 2), sequenceAfter1.store⟩

def sequenceResult : Config :=
  ⟨.skip, sequenceAfter2.store.insert "l" 2⟩

theorem sequence_step1 : Step sequenceStart sequenceAfter1 :=
  .seqStep (.assignValue (by decide))

theorem sequence_step2 : Step sequenceAfter1 sequenceAfter2 := .seqSkip

theorem sequence_step3 : Step sequenceAfter2 sequenceResult :=
  .assignValue (by decide)

theorem sequence_left_first_trace :
    lts.MTr sequenceStart [(), (), ()] sequenceResult :=
  .stepL sequence_step1 (.stepL sequence_step2 (.stepL sequence_step3 .refl))

theorem sequence_result_store :
    Store.lookup sequenceResult.store "l" = some 2 := by
  simp [sequenceResult]

end Silmaril.Courses.Cambridge.L1.Exercises
