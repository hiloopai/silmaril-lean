module

public import Silmaril.Cerberus.Elaboration.NullPointers.Defs

/-! Selected pinned branch equations over the actual explicit translation state.
The schedule retains discarded child effects and all three unused allocations. -/
@[expose] public section
namespace Silmaril.Cerberus.Elaboration.NullPointers
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Construction

/-- An int-pointer cast of zero does not take the whole-expression fast path. -/
theorem integer_pointer_cast_is_not_null (category : Ail.GenTypeCategory)
    (annotations typeAnnotations referencedAnnotations : List Annot)
    (location : Loc) (castQualifiers pointerQualifiers : Qualifiers)
    (integerType : IntegerType) (operand : Ail.TypedExpression) :
    isNullPointerConstant (.mk category annotations location
      (.cast castQualifiers (.mk typeAnnotations (.pointer pointerQualifiers
        (.mk referencedAnnotations (.basic (.integer integerType))))) operand)) = false := rfl

/-- The child action is evaluated between the second and third allocations;
no successful child evaluation or desired Core value is supplied as a premise. -/
theorem cast_integer_schedule (config : Target.Config) (notCheri : config.cheri = false)
    (sourceAnnotations destinationAnnotations : List Annot) (integerType : IntegerType)
    (qualifiers : Qualifiers) (referenced : Ctype) (operand : Ail.TypedExpression)
    (isNull : isNullPointerConstant operand = true) (child : State.ElabM Effect) :
    castInteger config (.mk sourceAnnotations (.basic (.integer integerType)))
      (.mk destinationAnnotations (.pointer qualifiers referenced)) operand child = (do
        let _ ← State.wrappedFreshSymbol (.loaded .integer)
        let _ ← State.wrappedFreshSymbol (.object .integer)
        let _ ← child
        let _ ← State.freshDescription .none
        return addStandard "§6.5.4" (pureEffect (specified (nullptr referenced)))) := by
  simp [castInteger, notCheri, isNull]

end Silmaril.Cerberus.Elaboration.NullPointers
