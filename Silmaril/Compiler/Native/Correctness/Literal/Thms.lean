module

public import Silmaril.Compiler.Native.Correctness.Literal.Defs
public import Silmaril.Compiler.Core.ElaborationProcess.Thms
@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.Literal
open Silmaril.Cerberus
open Silmaril.Compiler.Core.ElaborationProcess

/-- The independent literal-input predicate proves actual Functions success. -/
theorem elaborates {source : Source} (admitted : elaborationDomain source) :
    ∃ bindings, elaborate source = .ok bindings := by
  obtain ⟨literal, shape, available, _, conversion, resultType, parameters, body, found⟩ := admitted
  refine ⟨literal.bindings source.elaboration.runtime source.elaboration.freshness conversion, ?_⟩
  unfold elaborate
  rw [shape]
  exact congrArg Prod.fst (literal_elaborate source.elaboration.config source.types
    source.elaboration.runtime literal source.elaboration.freshness available
    conversion resultType parameters body found)

/-- Coverage holds for the stated elaboration domain independently of whether
native compilation accepts its members. This proves no native validity. -/
theorem coverage : Task.elaborationCoversAccepted elaborationDomain := by
  intro source _ _
  exact elaborates source.property.1

/-- A future coherent native milestone may strengthen the input predicate and
reuse the same proved source coverage without changing source semantics. -/
theorem coverage_on (domain : Source → Prop)
    (included : ∀ source, domain source → elaborationDomain source) :
    Task.elaborationCoversAccepted domain := by
  intro source _ _
  exact elaborates (included source.val source.property.1)

end Silmaril.Compiler.Native.Correctness.Literal
