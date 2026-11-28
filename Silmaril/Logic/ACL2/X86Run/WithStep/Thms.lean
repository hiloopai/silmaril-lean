module

public import Silmaril.Logic.ACL2.X86Run.WithStep.Defs
public import Silmaril.Logic.ACL2.X86Step.Thms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.WithStep

set_option maxRecDepth 4096 in
/-- The step symbol in the run model has the checked source body as its denotation. -/
theorem step_defining_equation (bindings : FrontierBindings) (x86 : Standard.Object) :
    (machineBindings bindings).admittedModel.interpret
        (declaration.inclusion.symbol stepSymbol) (fun _ => x86) =
      X86Step.definition.body.eval bindings (fun _ => x86) := by
  change fetchDecodeExecute bindings x86 = _
  exact X86Step.defining_equation bindings x86

/-- The model satisfies the original recursive defining equation. -/
theorem run_equation_holds (bindings : FrontierBindings) :
    (declaration.equation runSymbol).Holds (machineBindings bindings).admittedModel :=
  (machineBindings bindings).equation_holds

/-- The exact exported X86-RUN-HALTED sentence holds in the same model. -/
theorem halted_holds (bindings : FrontierBindings) :
    halted.Holds (machineBindings bindings).admittedModel :=
  Status.Tlb.halted_holds_with_record (fetchDecodeExecute bindings)

end Silmaril.Logic.ACL2.X86Run.WithStep
