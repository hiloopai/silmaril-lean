module

public import Silmaril.Compiler.Native.Correctness.SpecificationTransport.Defs
public import Silmaril.Compiler.Native.Correctness.Institution.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.SpecificationTransport

universe u

/-- Behavioral inclusion is exactly preservation of all universal predicates
over the same observations. This statement does not assert that either set is
nonempty, or identify observations of different languages without a convention. -/
theorem behavior_inclusion_iff_specification_transport {Behavior : Type u}
    (source target : Set Behavior) :
    target ⊆ source ↔
      ∀ specification : Set Behavior, source ⊆ specification → target ⊆ specification := by
  constructor
  · intro refinement specification satisfied
    exact refinement.trans satisfied
  · intro preserves
    exact preserves source (fun _ behavior => behavior)

/-- The canonical specialization uses exactly the existing native execution
and loading relation, rather than an independently chosen semantics. -/
theorem against_native (domain : Source → Prop) (toolchain : Toolchain domain) :
    Against domain (targetBehaviors toolchain) = Task.machineRefinement domain toolchain := rfl

/-- Complete behavioral refinement transports correctness to a stricter
target semantics. A subset of one-step transitions alone does not establish
this premise: removing steps can introduce new deadlocked behaviors. -/
theorem against_of_target_inclusion {domain : Source → Prop}
    {strict loose : Target → Set Observation}
    (comparison : ∀ target, strict target ⊆ loose target)
    (correct : Against domain loose) : Against domain strict := by
  intro source target accepted
  exact (behavior_inclusion_iff_specification_transport (loose target) (strict target)).mp
    (comparison target) (sourceBehaviors source.val) (correct source target accepted)

/-- The universal-specification presentation is exactly the existing actual
machine-refinement obligation. It cannot discharge that obligation by changing
its logical presentation or by registering an institution/Hets edge. -/
theorem machineRefinement_iff_preservesSpecifications (domain : Source → Prop)
    (toolchain : Toolchain domain) :
    Task.machineRefinement domain toolchain ↔ PreservesSpecifications domain toolchain := by
  constructor
  · intro refinement source target accepted specification satisfied
    exact Institution.preserves_projected_specification domain toolchain refinement
      accepted satisfied
  · intro preserves source target accepted
    exact preserves source target accepted (sourceBehaviors source.val)
      (fun _ behavior => behavior)

/-- A stricter allowed-observation predicate implies a weaker one. A verified
compiler therefore transports a source proof of the stricter predicate to the
weaker target predicate. The converse requires a separate proof. -/
theorem preserves_weaker_specification (domain : Source → Prop)
    (toolchain : Toolchain domain) (refinement : Task.machineRefinement domain toolchain)
    {source : Program domain} {target : Target} (accepted : run source = some target)
    {strict loose : Set Observation} (weaker : strict ⊆ loose)
    (satisfied : (sourceLanguage domain).Sat source strict) :
    (targetLanguage toolchain).Sat target loose := by
  have transported := Institution.preserves_projected_specification domain toolchain
    refinement accepted satisfied
  exact fun _ behavior => weaker (transported behavior)

/-- A stricter target semantics has fewer behaviors. Correctness against a
looser target semantics therefore implies correctness against the stricter one,
with the same source domain and actual compiler. Comparing toolchains still
requires an explicit inclusion proof, including stops and divergence. -/
theorem machineRefinement_of_target_inclusion (domain : Source → Prop)
    (strict loose : Toolchain domain)
    (comparison : ∀ target, targetBehaviors strict target ⊆ targetBehaviors loose target)
    (correct : Task.machineRefinement domain loose) :
    Task.machineRefinement domain strict := by
  exact against_of_target_inclusion comparison correct

/-- Nonempty target behavior requires both a load of this exact assembly/argv
and an execution observation of that image. Universal predicate transport alone
does not produce either witness. A stop or divergence is an observation, not a
proof that the program returned successfully. -/
theorem targetBehaviors_nonempty_iff {domain : Source → Prop}
    (toolchain : Toolchain domain) (target : Target) :
    (targetBehaviors toolchain target).Nonempty ↔
      ∃ image, toolchain.loads target.assembly target.arguments image ∧
        ∃ observation, Realises image.exit image.initial observation := by
  constructor
  · rintro ⟨observation, image, loaded, execution⟩
    exact ⟨image, loaded, observation, execution⟩
  · rintro ⟨image, loaded, observation, execution⟩
    exact ⟨observation, image, loaded, execution⟩

end Silmaril.Compiler.Native.Correctness.SpecificationTransport
