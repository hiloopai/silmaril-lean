module

public import Silmaril.Cerberus.Elaboration.Runtime.Defs

/-! The four scalar branches of `translation_aux.lem:383-406` at Cerberus
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`. Runtime calls retain the actual
destination CType, including annotations. Float-to-float is the source's
identity TODO, not a newly proved floating conversion. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Conversion
open Silmaril.Cerberus
open Construction

def loadedArithmetic (bindings : List Runtime.Binding) (source destination : Ctype)
    (expression : Pure) : Except String Pure :=
  match source, destination with
  | .mk _ (.basic (.integer _)), .mk _ (.basic (.integer _)) =>
      Runtime.standardCall bindings "conv_loaded_int" [ailCtype destination, expression]
  | .mk _ (.basic (.integer _)), .mk _ (.basic (.floating _)) =>
      Runtime.standardCall bindings "loaded_fvfromint" [ailCtype destination, expression]
  | .mk _ (.basic (.floating _)), .mk _ (.basic (.integer _)) =>
      Runtime.standardCall bindings "loaded_ivfromfloat" [ailCtype destination, expression]
  | .mk _ (.basic (.floating _)), .mk _ (.basic (.floating _)) => .ok expression
  | .mk _ (.basic (.integer _)), _
  | .mk _ (.basic (.floating _)), _ =>
      .error "Translation_aux.conv_loaded_arith, not (is_arithmetic ty_dst)"
  | _, _ => .error "Translation_aux.conv_loaded_arith, not (is_arithmetic ty_src)"

end Silmaril.Cerberus.Elaboration.Conversion
