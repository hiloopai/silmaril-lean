module

public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.Arithmetic
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Construction

/-- Add's direct conversion retains the actual Core `convInt` constructor. -/
theorem convert_direct (bindings : List Runtime.Binding) (type : IntegerType) (value : Pure) :
    convert bindings true type value = .ok (convertInteger type value) := rfl

/-- Mul/sub conversion uses the genuine named runtime function. -/
theorem convert_runtime (bindings : List Runtime.Binding) (type : IntegerType) (value : Pure) :
    convert bindings false type value = Runtime.standardCall bindings "conv_int"
      [ailCtype (.mk [] (.basic (.integer type))), value] := rfl

/-- Usual arithmetic conversion ignores source annotations for equal integer
Ctypes and constructs both signed-int conversion destinations without them. -/
theorem usual_signed_int (config : Target.Config) (env : Target.Environment)
    (bindings : List Runtime.Binding) (direct : Bool) (leftAnnotations rightAnnotations : List Annot)
    (left right : Pure) (ordinary : config.cheri = false) :
    usualArithmetic config env bindings direct
      (.mk leftAnnotations (.basic (.integer (.signed .int))))
      (.mk rightAnnotations (.basic (.integer (.signed .int)))) left right =
    convertPair bindings direct (.signed .int) left right := by
  simp only [usualArithmetic, ordinary, Bool.false_eq_true, ↓reduceIte, floatingType,
    promoteType, GeneralizedTypes.promote, Target.integerEqual]
  rfl

theorem signed_overflow (config : Target.Config) (env : Target.Environment)
    (annotations : List Annot) (base : IntegerBaseType) (operator : IntOp)
    (left right fallback : Pure) :
    withIntegerBehavior config env (.mk annotations (.basic (.integer (.signed base))))
      operator left right fallback = .ok (catchExceptionalCondition (.signed base) operator left right) := rfl

theorem unsigned_wrap (config : Target.Config) (env : Target.Environment)
    (annotations : List Annot) (base : IntegerBaseType) (operator : IntOp)
    (left right fallback : Pure) :
    withIntegerBehavior config env (.mk annotations (.basic (.integer (.unsigned base))))
      operator left right fallback = .ok (wrapInteger (.unsigned base) operator left right) := rfl

/-- Keep the exact upstream subtraction tag, despite its section-number typo. -/
theorem subtraction_standards : operatorData .sub =
    .ok (.sub, .sub, "§6.5.6", "§6.5.6#4", "§6.5.6#6", "§6.5.5#6") := rfl

end Silmaril.Cerberus.Elaboration.Arithmetic
