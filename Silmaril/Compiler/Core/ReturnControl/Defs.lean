module

public import Silmaril.Compiler.Core.ElaborationTotal.Thms
@[expose] public section
namespace Silmaril.Compiler.Core.ReturnControl
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration.Construction

/-- The concrete signed-int type used by the generic loaded-int return. -/
def signedIntType : Ctype := .mk [] (.basic (.integer (.signed .int)))

/-- Actual Core return-label transfer through a recognized conversion function. -/
def convertedReturn (label conversion occurrence : Sym) : Effect :=
  run label [call (.sym conversion) [ctype signedIntType, symbolPure occurrence]]

end Silmaril.Compiler.Core.ReturnControl
