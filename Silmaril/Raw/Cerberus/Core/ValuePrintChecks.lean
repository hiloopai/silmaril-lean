module

public import Silmaril.Cerberus.Core.Outcome.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta import Silmaril.Cerberus.Ctype.Defs

/-! Exit observation preserves loaded uncertainty and printable Core values. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

/-- Unspecified exits retain their type rather than choosing an integer. -/
theorem unspecified_exit (t : Ctype) (text : String)
    (h : typeText 254 t = some text) :
    observation (some (.defined (.loaded (.unspecified t)))) =
      {status := "Defined", printedValue := some ("Unspecified('" ++ text ++ "')")} := by
  simp [observation, valueText, loadedText, h]

theorem unit_exit : observation (some (.defined .unit)) =
    {status := "Defined", printedValue := some "Unit"} := by decide +kernel

theorem boolean_exit : observation (some (.defined .false)) =
    {status := "Defined", printedValue := some "False"} := by decide +kernel

private def intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))
private theorem pointer_exit : valueText 256 (.loaded (.specified (.pointer (.null intTy)))) =
    some "Specified(NULL(signed int))" := by decide +kernel
#guard valueText 256 (.tuple [.unit, .true, integer (-1)]) ==
    some "(Unit, True, -1)"
#guard valueText 256 (.loaded (.unspecified (.mk [] (.array intTy (some 3))))) ==
    some "Unspecified('signed int[3]')"
private theorem function_pointer_exit : valueText 256 (.object (.pointer (.function (.mk ⟨[100]⟩ 1 (.id "f"))))) =
    some "Cfunction(f)" := by decide +kernel
#guard valueText 256 (.object (.pointer (.allocated 2 256))) ==
    some "(@2, 0x100)"

end Silmaril.Cerberus.Core.Dynamics
