module

public import Silmaril.Cerberus.Core.PureOperands.Thms

@[expose] public section
namespace Silmaril.Cerberus.Core.DiagnosticOperands
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- The actual diagnostic focusing performed by these constant operand
annotations. Only the diagnostic location may change. -/
def focused (memory : Mem.Concrete.State) : Mem.Concrete.State :=
  if libraryLocation .unknown then memory else {memory with currentLocation := .unknown}

end Silmaril.Cerberus.Core.DiagnosticOperands
