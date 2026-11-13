module

public import Silmaril.Cerberus.Elaboration.ControlTests.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ControlTests
open Silmaril.Cerberus

/-- A concrete integer input keeps its exact category, location and annotations
on the generated octal zero, while the test result is concrete signed int. -/
theorem equalZero_integer (config : Target.Config) (env : Target.Environment)
    (type : IntegerType) (annotations : List Annot) (location : Loc)
    (node : Ail.ExpressionNode Ail.GenTypeCategory) :
    equalZero config env (.mk (.rvalue (.basic (.integer (.concrete type)))) annotations location node) =
    .ok (.mk signedIntCategory annotations location
      (.binary (.mk (.rvalue (.basic (.integer (.concrete type)))) annotations location node) .eq
        (.mk (.rvalue (.basic (.integer (.concrete type)))) annotations location
          (.const (.integer (.iconstant 0 .octal none)))))) := rfl

end Silmaril.Cerberus.Elaboration.ControlTests
