module

public import Silmaril.Logic.ACL2.X86Step.Defs
public import Silmaril.Logic.ACL2.X86Run.Status.TlbThms

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.WithStep

/-- The 33 named, arity-indexed external operations of the checked logical step. -/
abbrev FrontierBindings := Translated.Interpretation X86Step.frontier

/-- Use the interpretation of the checked unary declaration at the step symbol. -/
def fetchDecodeExecute (bindings : FrontierBindings) (x86 : Standard.Object) : Standard.Object :=
  X86Step.definition.extend bindings X86Step.definition.symbol (fun _ => x86)

/-- Bind the recursive run to the checked step and the existing record readers. -/
def machineBindings (bindings : FrontierBindings) : MachineBindings :=
  Status.Tlb.machineBindingsWithRecord (fetchDecodeExecute bindings)

end Silmaril.Logic.ACL2.X86Run.WithStep
