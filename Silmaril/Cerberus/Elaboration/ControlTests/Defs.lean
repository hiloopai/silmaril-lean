module

public import Silmaril.Cerberus.GeneralizedTypes.Defs

/-! Integer TestEq synthesis from pinned `translation.lem:94-114`. This creates
actual typed-Ail syntax, retaining the original category on the octal-zero
child and copying annotations/location. Floating and pointer test synthesis
remain outside this focused helper, as do statement lowering and scheduling. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.ControlTests
open Silmaril.Cerberus

def signedIntCategory : Ail.GenTypeCategory :=
  .rvalue (.basic (.integer (.concrete (.signed .int))))

def integerType : Ctype → Bool
  | .mk _ (.basic (.integer _)) => true
  | _ => false

/-- Source `mkTestExpression TestEq e` in its integer accepted domain. -/
def equalZero (config : Target.Config) (env : Target.Environment)
    (input : Ail.TypedExpression) : Except String Ail.TypedExpression := do
  let type ← (GeneralizedTypes.expressionType config env input).mapError reprStr
  unless integerType type do
    throw "unsupported: integer control test required"
  let .mk category annotations location _ := input
  let zero := Ail.Expression.mk category annotations location
    (.const (.integer (.iconstant 0 .octal none)))
  return .mk signedIntCategory annotations location (.binary input .eq zero)

end Silmaril.Cerberus.Elaboration.ControlTests
