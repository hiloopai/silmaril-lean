module

public import Silmaril.Cerberus.Elaboration.Construction.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Construction
open Silmaril.Cerberus
open Silmaril.Cerberus.Core

/-- Singleton tuples preserve their existing annotations and node exactly. -/
theorem tuplePattern_singleton (pattern : Pat) : tuplePattern [pattern] = .ok pattern := rfl
theorem tuplePure_singleton (expression : Pure) : tuplePure [expression] = .ok expression := rfl

theorem maybeAnnotateInteger_atomic (annotations : List Annot) (type : Ctype) (expression : Pure) :
    maybeAnnotateInteger (.mk annotations (.atomic type)) expression = expression := rfl

theorem negate_shape (type : IntegerType) (expression : Pure) :
    negate type expression = .mk [] ()
      (.op .sub (.mk [.value (.integer type)] () (.val (.object (.integer 0)))) expression) := rfl

theorem unseq_singleton (expression : Effect) : unseq [expression] = expression := rfl
theorem unseqEffect_singleton (expression : Effect) :
    unseqEffect [expression] = .mk [] (.unseq [expression]) := rfl

theorem addAttributes_empty (expression : Effect) : addAttributes (.mk []) expression = expression := rfl

end Silmaril.Cerberus.Elaboration.Construction
