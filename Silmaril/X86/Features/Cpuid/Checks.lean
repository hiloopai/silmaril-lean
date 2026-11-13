module

public import Silmaril.X86.Features.Cpuid.Dispatch
public import Silmaril.X86.Features.Cpuid.Models

/-!
# Checks of the CPUID model and the dispatch kit

* The dispatch hypotheses are satisfiable both ways: `nehalem` is a consistent
  x86-64 profile with POPCNT, `core2duo` one without (`popcnt_hyps_sat`), so a
  dispatch theorem over all consistent profiles covers both branches.
* `popcnt_test` agrees with every dumped model (`popcnt_test_models`), and so
  does `Observed` (`observed_models`).
* An inconsistent profile breaks the link: `liar` reports POPCNT in CPUID but
  does not execute it (`liar_not_consistent`, `liar_observes`), which is why the
  dispatch theorems assume `Consistent`.
* XGETBV is #UD on `qemu64` (no OSXSAVE) and reads XCR0 = 7 on `haswell`
  (`xgetbv_qemu64`, `xgetbv_haswell`).
* `cpuid_cases` closes a two-branch goal (`cases_demo`).
-/

@[expose] public section

namespace Silmaril.X86.Features.Cpuid.Checks

open Silmaril.X86.Features
open Silmaril.X86.Features.Profile

/-- Both branches of a POPCNT dispatch happen on consistent x86-64 profiles. -/
theorem popcnt_hyps_sat :
    (nehalem.Consistent ∧ FeatureSet.baseline64 ⊆ nehalem.features ∧ Feature.popcnt ∈ nehalem.features) ∧
    (core2duo.Consistent ∧ FeatureSet.baseline64 ⊆ core2duo.features ∧ Feature.popcnt ∉ core2duo.features) :=
  ⟨⟨ofCase_consistent 4, by decide, by decide⟩, ⟨ofCase_consistent 3, by decide, by decide⟩⟩

/-- The compiled test `ecx & 0x800000` agrees with POPCNT membership on every model. -/
theorem popcnt_test_models :
    models.all (fun p => ((p.cpuid 1 0).ecx &&& 0x800000#32 != 0) == p.features.has .popcnt) =
      true := by
  decide

/-- `Observed` is membership on every model, for every feature. -/
theorem observed_models : ∀ p ∈ models, ∀ f, p.Observed f ↔ f ∈ p.features :=
  fun p hp _ => observed_iff (models_consistent p hp)

/-- A profile whose CPUID claims POPCNT but whose semantics do not execute it. -/
def liar : Profile := { nehalem with name := "liar", features := core2duo.features }

theorem liar_not_consistent : ¬ liar.Consistent := by
  unfold Consistent; decide

theorem liar_observes : liar.Observed .popcnt ∧ Feature.popcnt ∉ liar.features := by
  refine ⟨⟨by decide, by decide, .inl rfl⟩, by decide⟩

/-- A core with ECX = 0. -/
def core0 : X86.State :=
  { regs := fun _ => 0, rip := 0x1000, flags := ⟨none, none, none, none, none, none⟩ }

theorem xgetbv_qemu64 (m : Process.Memory) :
    sysExec qemu64 .xgetbv 3 (State.ofCore core0) m = .fault .invalidOpcode := by
  simp only [sysExec, show qemu64.osxsave = false by decide, Bool.not_false, ite_true]

theorem haswell_osxsave : haswell.osxsave = true := by decide

theorem haswell_xcr0 : haswell.xcr0 = 7 := by decide

theorem xgetbv_haswell (m : Process.Memory) :
    sysExec haswell .xgetbv 3 (State.ofCore core0) m =
      Result.pure (fun s => s.setCore (xgetbvState 7 s.core)) 3 (State.ofCore core0) m := by
  simp only [sysExec, haswell_osxsave, haswell_xcr0, Bool.not_true]
  rfl

theorem xgetbv_haswell_rax :
    (xgetbvState haswell.xcr0 core0).read .rax = 7 := by
  rw [(xgetbvState_read _ _).1, haswell_xcr0]; rfl

/-- `cpuid_cases` on a two-branch goal. -/
theorem cases_demo (p : Profile) (hp : p.Consistent) (hb : FeatureSet.baseline64 ⊆ p.features) :
    ((p.cpuid 1 0).ecx.getLsbD 23 = true → Feature.popcnt ∈ p.features) ∧
    ((p.cpuid 1 0).ecx.getLsbD 23 = false → Feature.popcnt ∉ p.features) := by
  cpuid_cases hp hb Feature.popcnt with hbit hmem
  · exact ⟨fun _ => hmem, fun h => absurd (hbit.symm.trans h) (by decide)⟩
  · exact ⟨fun h => absurd (hbit.symm.trans h) (by decide), fun _ => hmem⟩

end Silmaril.X86.Features.Cpuid.Checks
