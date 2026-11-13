module

public import Silmaril.Compiler.Native.Correctness.Institution.Defs
/-! Universal specifications of the actual native compiler's observations.
This contract neither chooses a toolchain nor proves compilation, loading,
completion, absence of undefined behavior or native machine refinement. -/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.SpecificationTransport

/-- Correctness against an explicit family of complete target behaviors, at
the fixed source domain, actual compiler and observation type. A different
operational semantics must supply its stops and infinite executions too.
Loading, ABI/environment agreement and nonvacuity remain separate obligations. -/
def Against (domain : Source → Prop) (semantics : Target → Set Observation) : Prop :=
  ∀ (source : Program domain) (target : Target), run source = some target →
    semantics target ⊆ sourceBehaviors source.val

/-- Every successful actual compilation preserves every universally satisfied
specification at the fixed native observation convention. Finite stops and
infinite executions remain observations; no successful-return filter is added. -/
def PreservesSpecifications (domain : Source → Prop) (toolchain : Toolchain domain) : Prop :=
  ∀ (source : Program domain) (target : Target), run source = some target →
    ∀ specification : Set Observation,
      (sourceLanguage domain).Sat source specification →
        (targetLanguage toolchain).Sat target specification

end Silmaril.Compiler.Native.Correctness.SpecificationTransport
