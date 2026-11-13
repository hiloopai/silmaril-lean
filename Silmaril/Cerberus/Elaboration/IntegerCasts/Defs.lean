module

public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.Conversion.Defs

/-! The non-CHERI direct integer-to-integer cast branch from pinned Cerberus
`translation.lem:1862-1871,1911-1913`. Both wrappers and the final unused let
symbol are allocated around the actual recursive child computation. Conversion
is the actual named loaded-integer runtime call, retaining its destination CType
and specified/unspecified input. Floating, pointer and CHERI casts are separate.
-/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.IntegerCasts
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

/-- Actual selected cast equation; the child's translated Core is weakly bound
before calling `conv_loaded_int`. The unused object wrapper and let allocation
still consume the shared source freshness history. -/
def translate (config : Target.Config) (bindings : List Runtime.Binding)
    (source destination : Ctype) (child : State.ElabM Effect) : State.ElabM Effect := do
  if config.cheri then throw (.message "unsupported: CHERI integer cast elaboration")
  let .mk _ (.basic (.integer _)) := source
    | throw (.message "unsupported: integer cast source is not a direct integer")
  let .mk _ (.basic (.integer _)) := destination
    | throw (.message "unsupported: integer cast destination is not a direct integer")
  let loaded ← State.wrappedFreshSymbol (.loaded .integer)
  let _ ← State.wrappedFreshSymbol (.object .integer)
  let core ← child
  let _ ← State.freshDescription .none
  let converted ← Constants.liftResult
    (Conversion.loadedArithmetic bindings source destination loaded.expression)
  return addStandard "§6.5.4" (weakSequence loaded.pattern core (pureEffect converted))

end Silmaril.Cerberus.Elaboration.IntegerCasts
