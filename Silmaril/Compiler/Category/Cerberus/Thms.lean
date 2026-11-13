module

public import Silmaril.Compiler.Category.Cerberus.Defs
public import Silmaril.Cerberus.Institution.Thms
public import Silmaril.Compiler.Category.Pass.Defs

@[expose] public section
namespace Silmaril.Compiler.Category.Cerberus

open CategoryTheory Silmaril.Compile.Category

/-- Category satisfaction is exactly universal satisfaction of the actual Core
transition system, including nondeterministic and infinite executions. -/
theorem sat_iff (model : Core.Model) (sentence : Core.Sentence) :
    language.Sat model {behavior | sentence behavior} ↔ Core.Satisfies model sentence := Iff.rfl

/-- Identity-convention refinement uses the actual Core behavior relation. -/
theorem refines_iff (source target : Core.Model) :
    language.Refines source target ↔ target.Refines source :=
  ⟨fun refinement => refinement.2, fun refinement => ⟨rfl, refinement⟩⟩

/-- Core behavior sets are inhabited independently of any source elaborator or
compiler: their actual initial configurations have empty finite traces. -/
theorem beh_nonempty (model : Core.Model) : (language.beh model).Nonempty :=
  ⟨.finite [] model.initialState, Silmaril.Cerberus.Institution.initial_realises model⟩

/-- Validity at an explicit read-back convention means every actual target
behavior reads back to a genuine source Core behavior, with interface agreement.
The observation read-back is supplied, not inferred from code generation. -/
theorem valid_iff_readBack {target : Language.{0}} {convention : language ⟶ target}
    (readback : Convention.ReadBack convention) (source : Core.Model) (program : target.Prog) :
    Valid convention source program ↔
      convention.Φ (language.iface source) = target.iface program ∧
        ∀ behavior ∈ target.beh program, source.realises (readback.g behavior) := by
  refine (Silmaril.Compile.Category.valid_iff_readBack readback source program).trans ?_
  constructor
  · rintro ⟨interface, behaviors⟩
    exact ⟨interface, fun behavior member => behaviors ⟨behavior, member, rfl⟩⟩
  · rintro ⟨interface, behaviors⟩
    refine ⟨interface, ?_⟩
    rintro _ ⟨behavior, member, rfl⟩
    exact behaviors behavior member

/-- A domain-restricted compiler proof transports an actual Core specification.
The explicit premise quantifies over every accepted source in the selected input
domain; no premise claims the native driver or any unproved stage satisfies it.
Ail-to-Core correspondence, observation meaning and native execution semantics
must be supplied independently when instantiating this theorem. -/
theorem preserves_spec_on {target : Language.{0}} {convention : language ⟶ target}
    (readback : Convention.ReadBack convention) (domain : Core.Model → Prop)
    (compile : Core.Model → Option target.Prog)
    (sound : ∀ source, domain source → ∀ program,
      compile source = some program → Valid convention source program)
    {source : Core.Model} {program : target.Prog} {sentence : Core.Sentence}
    (admitted : domain source) (compiled : compile source = some program)
    (satisfies : Core.Satisfies source sentence) :
    target.Sat program {behavior | sentence (readback.g behavior)} := by
  have behaviors := ((valid_iff_readBack readback source program).1
    (sound source admitted program compiled)).2
  exact fun behavior member => satisfies _ (behaviors behavior member)

/-- A genuinely proved category pass is an immediate instance of the restricted
preservation theorem. This also applies to `Pipeline.toPass`; it constructs no
pass for the current native executable. -/
theorem pass_preserves_spec {target : Language.{0}} {convention : language ⟶ target}
    (readback : Convention.ReadBack convention) (pass : Pass convention)
    {source : Core.Model} {program : target.Prog} {sentence : Core.Sentence}
    (compiled : pass.run source = some program) (satisfies : Core.Satisfies source sentence) :
    target.Sat program {behavior | sentence (readback.g behavior)} :=
  preserves_spec_on readback (fun _ => True) pass.run
    (fun source _ program accepted => pass.sound source program accepted)
    trivial compiled satisfies

end Silmaril.Compiler.Category.Cerberus
