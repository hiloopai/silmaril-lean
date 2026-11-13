module

public import Silmaril.Cerberus.Elaboration.Conversion.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Conversion
open Silmaril.Cerberus
open Construction

/-- The annotated destination CType is passed through unchanged. -/
theorem loadedArithmetic_integer (bindings : List Runtime.Binding)
    (sourceAnnotations destinationAnnotations : List Annot) (source destination : IntegerType)
    (expression : Pure) :
    loadedArithmetic bindings (.mk sourceAnnotations (.basic (.integer source)))
      (.mk destinationAnnotations (.basic (.integer destination))) expression =
    Runtime.standardCall bindings "conv_loaded_int"
      [ailCtype (.mk destinationAnnotations (.basic (.integer destination))), expression] := rfl

theorem loadedArithmetic_floating_identity (bindings : List Runtime.Binding)
    (sourceAnnotations destinationAnnotations : List Annot) (source destination : FloatingType)
    (expression : Pure) :
    loadedArithmetic bindings (.mk sourceAnnotations (.basic (.floating source)))
      (.mk destinationAnnotations (.basic (.floating destination))) expression = .ok expression := rfl

end Silmaril.Cerberus.Elaboration.Conversion
