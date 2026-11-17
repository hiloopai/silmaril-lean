import Silmaril.Project.CTV.Examples.Defs
import Silmaril.Project.Shapes.CTV.Thms

/-!
# Whole-program validation examples (kernel-checked)

The registered rows (with the project's statement and axiom audit) are in `examples/c-tv/CTvRows.lean`;
this file keeps the remaining verdict checks (`unsupported`, `unknown`, the exit-status host).

Each verdict is computed by `cbv` (a proof the kernel checks) and turned into a statement of the
shapes by the validator's soundness theorems. Axioms: `propext`, `Classical.choice`, `Quot.sound`
(audited in `tests/cerberus/TVValidate.lean`).

This file is not a `module`: under the module system `cbv` does not finish on these Core runs
within minutes, while here each verdict takes seconds (docs/projects/c-tv.md, open obligations).

| theorem | statement |
|---|---|
| `fold_refines` | `return 3 + 0;` refines `return 1 + 2;` |
| `fold_refines_ub_free` | and the source has no undefined behaviour (`refines_ub_free`) |
| `overflow_not_ub_free` | the `INT_MAX + 1` row is not UB-free |
| `fold_equivalent` | and the two are equivalent |
| `wrong_fold_not_refines` | `return 2 + 2;` does not refine `return 1 + 2;` |
| `overflow_refined_by_anything` | a terminating supported target refines `INT_MAX + 1` (undefined behaviour); the report flags that coverage used only undefined behaviour |
| `overflow_not_refines` | `INT_MAX + 1` does not refine `return 2 + 2;` (target UB is refuted by its signal-0 witness) |
| `lowBit_refines`, `lowBit_lp64_not_refines` | with a one-bit exit status `return 0 + 1;` refines `return 1 + 2;`; with the POSIX status it does not |
| `noMain_unsupported` | a target without `main` is `unsupported`, not validated |
| `noMain_source_unknown` | a source without `main` gives `unknown`, not `refuted` |
| `shallow_unknown` | with a depth bound of 20 transitions the verdict is `unknown` |
-/


namespace Tests.CTV

open Silmaril.Project.CTV.Examples

open Silmaril.Cerberus
open Silmaril.Cerberus.TV
open Silmaril.Project.Shapes.CTV

theorem fold_validated : (validate Spec.Impl.lp64 (add 1 2) (add 3 0)).verdict = .validated := by
  cbv

theorem fold_refines : CRefines Spec.Impl.lp64 (add 1 2) (add 3 0) :=
  CRefines.of_validate {} fold_validated

theorem fold_refines_ub_free : CRefinesUBFree Spec.Impl.lp64 (add 1 2) (add 3 0) :=
  CRefinesUBFree.of_validate {} (by cbv)

/-- The overflow row is validated only through source UB: it is not a `refines_ub_free` row. -/
theorem overflow_not_ub_free : validateUBFree Spec.Impl.lp64 overflow (add 2 2) = false := by
  cbv

theorem fold_equivalent : CEquivalent Spec.Impl.lp64 (add 1 2) (add 3 0) :=
  CEquivalent.of_validate {} (by cbv)

theorem wrong_fold_refuted : (validate Spec.Impl.lp64 (add 1 2) (add 2 2)).verdict = .refuted := by
  cbv

theorem wrong_fold_not_refines : CNotRefines Spec.Impl.lp64 (add 1 2) (add 2 2) :=
  CNotRefines.of_validate {} wrong_fold_refuted

theorem overflow_validated : (validate Spec.Impl.lp64 overflow (add 2 2)).verdict = .validated ∧
    (validate Spec.Impl.lp64 overflow (add 2 2)).coveredOnlyByUB = true := by
  cbv

theorem overflow_refined_by_anything : CRefines Spec.Impl.lp64 overflow (add 2 2) :=
  CRefines.of_validate {} overflow_validated.1

theorem overflow_not_refines : CNotRefines Spec.Impl.lp64 (add 2 2) overflow :=
  CNotRefines.of_validate {} (by cbv)

theorem lowBit_refines : CRefines lowBitHost (add 1 2) (add 0 1) :=
  CRefines.of_validate {} (by cbv)

theorem lowBit_lp64_not_refines : CNotRefines Spec.Impl.lp64 (add 1 2) (add 0 1) :=
  CNotRefines.of_validate {} (by cbv)

theorem noMain_unsupported :
    (validate Spec.Impl.lp64 (add 1 2) noMain).verdict = .unsupported := by
  cbv

theorem noMain_source_unknown :
    (validate Spec.Impl.lp64 noMain (add 1 2)).verdict = .unknown := by
  cbv

theorem shallow_unknown :
    (validate Spec.Impl.lp64 (add 1 2) (add 3 0) { depth := 20 }).verdict = .unknown := by
  cbv

end Tests.CTV
