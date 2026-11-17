import Silmaril.Project.Shapes.CTV.Thms
import Silmaril.Project.CTV.Examples.Defs

/-!
# The C translation-validation rows (`silmaril/c-tv.toml`)

Every row is solved (`@[solves]`) or refuted (`@[refutes]`) by a theorem whose statement is the row,
so `sil project check` audits the declaration, its statement and its axioms. Verdicts and coherence
facts are computed by `cbv`, a proof the kernel checks; nothing here is evaluated natively.

This library is not a `module`: under the module system the same `cbv` runs of the Core dynamics
are two orders of magnitude slower (a six-transition prefix of `return 1 + 2;` did not finish in
three minutes, the whole validation takes seconds here). docs/projects/c-tv.md keeps it as an open
obligation.
-/

silmaril load "silmaril/c-tv.toml"

open Silmaril.Cerberus Silmaril.Cerberus.TV Silmaril.Project.Shapes.CTV Silmaril.Project.CTV.Examples

namespace CTvRows

set_option maxRecDepth 100000

theorem fold_validated : (validate Spec.Impl.lp64 foldSource foldTarget).verdict = .validated := by cbv

@[solves "silmaril.c_tv.examples.fold.refines"] theorem fold_refines : silmaril.c_tv.examples.fold.refines :=
  CRefines.of_validate {} fold_validated

@[solves "silmaril.c_tv.examples.fold.refines_ub_free"] theorem fold_refines_ub_free :
    silmaril.c_tv.examples.fold.refines_ub_free :=
  CRefinesUBFree.of_validate {} (by cbv)

@[solves "silmaril.c_tv.examples.fold.equivalent"] theorem fold_equivalent : silmaril.c_tv.examples.fold.equivalent :=
  CEquivalent.of_validate {} (by cbv)

@[refutes "silmaril.c_tv.examples.wrong_fold.refines"] theorem wrong_fold_not_refines :
    ¬ silmaril.c_tv.examples.wrong_fold.refines :=
  CNotRefines.of_validate (impl := Spec.Impl.lp64) {} (by cbv)

/-- Validated, but only through source undefined behaviour (`coveredOnlyByUB`). -/
theorem overflow_validated : (validate Spec.Impl.lp64 overflow overflowTarget).verdict = .validated ∧
    (validate Spec.Impl.lp64 overflow overflowTarget).coveredOnlyByUB = true := by cbv

@[solves "silmaril.c_tv.examples.overflow.refines"] theorem overflow_refines : silmaril.c_tv.examples.overflow.refines :=
  CRefines.of_validate {} overflow_validated.1

/-- The `INT_MAX + 1` source reaches undefined behaviour, so the row is not a UB-free refinement. -/
@[refutes "silmaril.c_tv.examples.overflow.refines_ub_free"] theorem overflow_not_ub_free :
    ¬ silmaril.c_tv.examples.overflow.refines_ub_free := by
  intro h
  have hub : (overflow.explore {}).ub = true ∧ (overflow.explore {}).limited = false := by cbv
  obtain ⟨o, out, hmem, hu⟩ : ∃ o out, (o, out) ∈ (overflow.explore {}).ends ∧ Outcome.isUB o = true := by
    have := hub.1; unfold Leaves.ub at this
    obtain ⟨⟨o, out⟩, hm, hu⟩ := List.any_eq_true.mp this
    exact ⟨o, out, hm, hu⟩
  have := h.sourceUBFree o out (Closed.explore_sound overflow {} (o, out) hmem)
  rw [hu] at this; cases this

@[solves "silmaril.c_tv.examples.fold.applies"] theorem fold_applies : silmaril.c_tv.examples.fold.applies := by
  unfold silmaril.c_tv.examples.fold.applies ProfileApplies; cbv

@[solves "silmaril.c_tv.examples.fold.refines_on"] theorem fold_refines_on : silmaril.c_tv.examples.fold.refines_on :=
  CRefinesOn.of_validate {} (by cbv) (by cbv) (by cbv)

@[refutes "silmaril.c_tv.examples.float_signature.applies"] theorem float_signature_not_applies :
    ¬ silmaril.c_tv.examples.float_signature.applies := by
  unfold silmaril.c_tv.examples.float_signature.applies ProfileApplies Profile.AppliesTo
  cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.bool"] theorem coherent_bool : silmaril.c_tv.profile.linux_x86_64.bool := by
  unfold silmaril.c_tv.profile.linux_x86_64.bool ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.char"] theorem coherent_char : silmaril.c_tv.profile.linux_x86_64.char := by
  unfold silmaril.c_tv.profile.linux_x86_64.char ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.schar"] theorem coherent_schar : silmaril.c_tv.profile.linux_x86_64.schar := by
  unfold silmaril.c_tv.profile.linux_x86_64.schar ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.uchar"] theorem coherent_uchar : silmaril.c_tv.profile.linux_x86_64.uchar := by
  unfold silmaril.c_tv.profile.linux_x86_64.uchar ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.short"] theorem coherent_short : silmaril.c_tv.profile.linux_x86_64.short := by
  unfold silmaril.c_tv.profile.linux_x86_64.short ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.ushort"] theorem coherent_ushort : silmaril.c_tv.profile.linux_x86_64.ushort := by
  unfold silmaril.c_tv.profile.linux_x86_64.ushort ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.int"] theorem coherent_int : silmaril.c_tv.profile.linux_x86_64.int := by
  unfold silmaril.c_tv.profile.linux_x86_64.int ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.uint"] theorem coherent_uint : silmaril.c_tv.profile.linux_x86_64.uint := by
  unfold silmaril.c_tv.profile.linux_x86_64.uint ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.long"] theorem coherent_long : silmaril.c_tv.profile.linux_x86_64.long := by
  unfold silmaril.c_tv.profile.linux_x86_64.long ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.ulong"] theorem coherent_ulong : silmaril.c_tv.profile.linux_x86_64.ulong := by
  unfold silmaril.c_tv.profile.linux_x86_64.ulong ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.long_long"] theorem coherent_longLong : silmaril.c_tv.profile.linux_x86_64.long_long := by
  unfold silmaril.c_tv.profile.linux_x86_64.long_long ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.ulong_long"] theorem coherent_ulongLong : silmaril.c_tv.profile.linux_x86_64.ulong_long := by
  unfold silmaril.c_tv.profile.linux_x86_64.ulong_long ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.size"] theorem coherent_size : silmaril.c_tv.profile.linux_x86_64.size := by
  unfold silmaril.c_tv.profile.linux_x86_64.size ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.ptrdiff"] theorem coherent_ptrdiff : silmaril.c_tv.profile.linux_x86_64.ptrdiff := by
  unfold silmaril.c_tv.profile.linux_x86_64.ptrdiff ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.intptr"] theorem coherent_intptr : silmaril.c_tv.profile.linux_x86_64.intptr := by
  unfold silmaril.c_tv.profile.linux_x86_64.intptr ProfileCoherentAt Profile.CoherentAt; cbv

@[solves "silmaril.c_tv.profile.linux_x86_64.uintptr"] theorem coherent_uintptr : silmaril.c_tv.profile.linux_x86_64.uintptr := by
  unfold silmaril.c_tv.profile.linux_x86_64.uintptr ProfileCoherentAt Profile.CoherentAt; cbv

@[refutes "silmaril.c_tv.profile.linux_x86_64.wchar"] theorem incoherent_wchar : ¬ silmaril.c_tv.profile.linux_x86_64.wchar :=
  not_coherentAt_of (by cbv)

@[solves "silmaril.c_tv.profile.linux_x86_64.pointer"] theorem coherent_pointer : silmaril.c_tv.profile.linux_x86_64.pointer := by
  unfold silmaril.c_tv.profile.linux_x86_64.pointer ProfileCoherentAt Profile.CoherentAt; cbv

@[refutes "silmaril.c_tv.profile.linux_x86_64.float"] theorem incoherent_float : ¬ silmaril.c_tv.profile.linux_x86_64.float :=
  not_coherentAt_of (by cbv)

@[solves "silmaril.c_tv.profile.linux_x86_64.double"] theorem coherent_double : silmaril.c_tv.profile.linux_x86_64.double := by
  unfold silmaril.c_tv.profile.linux_x86_64.double ProfileCoherentAt Profile.CoherentAt; cbv

@[refutes "silmaril.c_tv.profile.linux_x86_64.long_double"] theorem incoherent_longDouble : ¬ silmaril.c_tv.profile.linux_x86_64.long_double :=
  not_coherentAt_of (by cbv)

/-- A decoy for the explorer's association test (`tools/silmaril-project/tests/explore/c.mjs`): its
name mentions a corpus program and a shape, its statement is neither, so `c-pages` must not list it. -/
theorem decoy_arithmetic_refines : (1 : Nat) + 2 = 3 := rfl

end CTvRows
