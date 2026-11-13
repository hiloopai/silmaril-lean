module

public import Silmaril.Compiler.Native.Correctness.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness

open Silmaril.Cerberus Silmaril.Compile.Category

/-- The return sentinel lies outside the loaded code, so execution cannot
succeed immediately by equating the entry point with its return address. -/
theorem Loaded.exit_ne_entry {arguments : List String} {image : Image}
    (loaded : Loaded arguments image) : image.exit ≠ image.entry := by
  have lower := loaded.2.1
  have upper := loaded.2.2.1
  have outside := loaded.2.2.2.1
  intro same
  rw [same] at outside
  rcases outside with before | after <;> omega

/-- A successful actual elaboration fixes the exact source behavior language;
no other wire bindings can be substituted for the returned file. -/
theorem sourceBehaviors_iff {source : Source} {bindings : Codec.FileBindings}
    (accepted : elaborate source = .ok bindings) (observation : Observation) :
    observation ∈ sourceBehaviors source ↔
      (Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments ∨
        Silmaril.Compile.Core.Spec.CoreBeh (document source bindings) source.arguments
          (observe observation)) := by
  constructor
  · rintro ⟨other, otherAccepted, allowed⟩
    have same : other = bindings := Except.ok.inj (otherAccepted.symm.trans accepted)
    simpa only [same] using allowed
  · intro allowed
    exact ⟨bindings, accepted, allowed⟩

/-- A certificate's domain contains an actually accepted whole program. -/
theorem Certificate.accepted {domain : Source → Prop} {toolchain : Toolchain domain}
    (certificate : Certificate domain toolchain) :
    ∃ source : Program domain, ∃ target, run source = some target := by
  obtain ⟨source, assembly, accepted⟩ := certificate.acceptedProgram
  exact ⟨source, ⟨assembly, source.val.arguments⟩, by simp only [run, accepted]⟩

/-- An empty admitted source domain cannot be certified. -/
theorem no_certificate_of_empty_domain (domain : Source → Prop) (toolchain : Toolchain domain)
    (empty : ∀ source, ¬ domain source) : ¬ Certificate domain toolchain := by
  intro certificate
  obtain ⟨source, _, _⟩ := certificate.acceptedProgram
  exact empty source.val source.property.1

/-- Rejecting every admitted program cannot satisfy certificate nonvacuity. -/
theorem no_certificate_of_rejectsAll (domain : Source → Prop) (toolchain : Toolchain domain)
    (rejects : ∀ (source : Program domain) assembly, compile source.val ≠ .ok assembly) :
    ¬ Certificate domain toolchain := by
  intro certificate
  obtain ⟨source, assembly, accepted⟩ := certificate.acceptedProgram
  exact rejects source assembly accepted

/-- A modeled target stop cannot be excused as a defined source behavior.
In particular, decoding gaps are proof obligations, not successful executions. -/
theorem sourceBehaviors_stopped_iff (source : Source) (state : NativeState)
    (outcome : Silmaril.X86.Features.Outcome) :
    (.stopped state outcome) ∈ sourceBehaviors source ↔
      ∃ bindings, elaborate source = .ok bindings ∧
        Silmaril.Compile.Core.Spec.CoreUB (document source bindings) source.arguments := by
  constructor
  · rintro ⟨bindings, elaborated, allowed⟩
    refine ⟨bindings, elaborated, ?_⟩
    cases allowed with
    | inl ub => exact ub
    | inr behavior => cases behavior
  · rintro ⟨bindings, elaborated, ub⟩
    exact ⟨bindings, elaborated, .inl ub⟩

/-- Category packaging consumes the explicit proof obligation; it supplies no
proof about lowering, optimization, decoding or native execution by itself. -/
def asPass (domain : Source → Prop) (toolchain : Toolchain domain)
    (refinement : Task.machineRefinement domain toolchain) :
    Pass (convention domain toolchain) where
  run := run
  sound source target accepted := by
    apply (valid_iff_beh _ _ _).2
    refine ⟨rfl, ?_⟩
    intro observation behavior
    exact ⟨observation, refinement source target accepted behavior, rfl⟩

theorem asPass_run (domain : Source → Prop) (toolchain : Toolchain domain)
    (refinement : Task.machineRefinement domain toolchain) (source : Program domain) :
    (asPass domain toolchain refinement).run source = run source := rfl

def Certificate.toPass {domain : Source → Prop} {toolchain : Toolchain domain}
    (certificate : Certificate domain toolchain) : Pass (convention domain toolchain) :=
  asPass domain toolchain certificate.machineRefinement

end Silmaril.Compiler.Native.Correctness
