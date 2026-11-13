module

public import Silmaril.Cerberus.Elaboration.IntegerCasts.Defs

/-! Selected source allocation, recursive-child and runtime conversion equations.
No successful elaboration or desired child Core is assumed by the schedule. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.IntegerCasts
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

/-- The source evaluates the child between the second and third allocations,
then converts its actual loaded result through the supplied runtime binding. -/
theorem integer_schedule (config : Target.Config) (notCheri : config.cheri = false)
    (bindings : List Runtime.Binding) (sourceAnnotations destinationAnnotations : List Annot)
    (sourceType destinationType : IntegerType) (child : State.ElabM Effect) :
    translate config bindings (.mk sourceAnnotations (.basic (.integer sourceType)))
      (.mk destinationAnnotations (.basic (.integer destinationType))) child = (do
        let loaded ← State.wrappedFreshSymbol (.loaded .integer)
        let _ ← State.wrappedFreshSymbol (.object .integer)
        let core ← child
        let _ ← State.freshDescription .none
        let converted ← Constants.liftResult (Runtime.standardCall bindings "conv_loaded_int"
          [ailCtype (.mk destinationAnnotations (.basic (.integer destinationType))), loaded.expression])
        return addStandard "§6.5.4" (weakSequence loaded.pattern core (pureEffect converted))) := by
  simp [translate, notCheri, Conversion.loadedArithmetic]

end Silmaril.Cerberus.Elaboration.IntegerCasts
