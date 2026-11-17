import Silmaril.Cerberus.TV.Validate.Thms
import Silmaril.Project.CTV.Examples.Defs
import tests.cerberus.TVExamples

/-! Audits of the whole-program validator (docs/projects/c-tv.md): the axioms of its soundness
theorems and of the kernel-checked example verdicts, and interpreted runs (`#guard`, evaluated by
the Lean interpreter, not the kernel) of the negative cases. -/

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Project.CTV.Examples

#print axioms Silmaril.Cerberus.TV.validate_sound
#print axioms Silmaril.Cerberus.TV.validate_refuted
#print axioms Silmaril.Cerberus.TV.validateEquivalent_sound
#print axioms Silmaril.Cerberus.TV.validateUBFree_sound
#print axioms Silmaril.Cerberus.TV.Closed.explore_complete
#print axioms Silmaril.Cerberus.TV.Closed.explore_terminates
#print axioms Tests.CTV.fold_refines
#print axioms Tests.CTV.wrong_fold_not_refines
#print axioms Tests.CTV.overflow_refined_by_anything
#print axioms Silmaril.Project.Shapes.CTV.linuxX86_64_coherentScalars

-- A target that is a gap is `unsupported`, never validated, whatever the source.
#guard (validate Spec.Impl.lp64 overflow noMain).verdict == .unsupported
-- A source that is a gap blocks refutation.
#guard (validate Spec.Impl.lp64 noMain (add 2 2)).verdict == .unknown
-- Budget exhaustion is `unknown` for both directions.
#guard (validate Spec.Impl.lp64 (add 1 2) (add 1 2) { budget := 10 }).verdict == .unknown
-- Reflexivity on a supported terminating program, without undefined behaviour.
#guard (validate Spec.Impl.lp64 (add 1 2) (add 1 2)).verdict == .validated
#guard !(validate Spec.Impl.lp64 (add 1 2) (add 1 2)).coveredOnlyByUB
-- Undefined behaviour in the source is reported when it is all the coverage rests on.
#guard (validate Spec.Impl.lp64 overflow (add 1 2)).coveredOnlyByUB

-- Abort coverage is prefix-aware when `abort` does not flush, and exact when it does.
example : covers Spec.Impl.lp64 (.aborted, "abc") (.aborted, "ab") = true := by decide +kernel
example : covers { Spec.Impl.lp64 with abortFlushes := true } (.aborted, "abc") (.aborted, "ab") = false := by
  decide +kernel
example : covers Spec.Impl.lp64 (.aborted, "ab") (.aborted, "abc") = false := by decide +kernel
