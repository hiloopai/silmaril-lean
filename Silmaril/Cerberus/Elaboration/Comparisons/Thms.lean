module

public import Silmaril.Cerberus.Elaboration.Comparisons.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Comparisons
open Silmaril.Cerberus
open Construction

/-- Comparison results use specified object integer constructors for 1/0,
rather than the loaded literal representation used by constant translation. -/
theorem booleanInteger_shape (condition : Pure) : booleanInteger condition =
    .mk [] () (.if_ condition (.mk [] () (.ctor .specified [integer 1]))
      (.mk [] () (.ctor .specified [integer 0]))) := rfl

theorem specifiedPair_shape (operands : Operands) : specifiedPair operands =
    .ok (.mk [] (.ctor .tuple [specifiedPattern operands.leftObject.pattern,
      specifiedPattern operands.rightObject.pattern])) := rfl

end Silmaril.Cerberus.Elaboration.Comparisons
