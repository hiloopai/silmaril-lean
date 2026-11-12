module

public import Silmaril.Cerberus.Core.Forced.Thms
public import Silmaril.Cerberus.Elaboration.Constants.Defs

/-! Actual Core unsequenced operand computations for canonical annotated
signed-int literals. Arbitrary integers, environments and continuations remain
parameters. No evaluator fuel, scheduler assumption or result runtime is used. -/
@[expose] public section
namespace Silmaril.Cerberus.Core.PureOperands
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration

/-- The real constant-expression elaborator's canonical output. -/
def constant (number : Int) : Construction.Effect :=
  .mk [.loc .unknown, .expr, .value (.integer (.signed .int))]
    (.pure (Constants.loadedInteger number))

end Silmaril.Cerberus.Core.PureOperands
