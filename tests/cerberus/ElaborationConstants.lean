import Silmaril.Cerberus.Elaboration.Constants.Thms
import Silmaril.Cerberus.Elaboration.Conversion.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Construction

private def context : State.Context := State.initial ⟨⟨[]⟩, 505, 1000⟩ .normal "Driver"
private def integerType : Ctype := .mk [.loc .unknown] (.basic (.integer (.signed .int)))
private def literal (annotations : List Annot := []) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.unknown (.iconstant 42 .decimal none)))))
    annotations .unknown (.const (.integer (.iconstant 42 .decimal none)))

-- Match the genuine constant-return expression field's loaded value and exact
-- annotation order, including the full-expression bound wrapper.
example : State.run (Constants.expression Target.pinnedApple Target.emptyEnvironment (literal [])) context =
    (.ok (.mk [.loc .unknown, .expr, .value (.integer (.signed .int))]
      (.pure (Constants.loadedInteger 42))), context) := by
  simp only [Constants.expression, literal, Constants.translateConstant]
  rfl
example : State.run (Constants.wrappedExpression Target.pinnedApple Target.emptyEnvironment (literal [])) context =
    (.ok (.mk [.std "§6.5#2"] (.bound (.mk [.loc .unknown, .expr, .value (.integer (.signed .int))]
      (.pure (Constants.loadedInteger 42))))), context) := by
  simp only [Constants.wrappedExpression, Constants.expression, literal, Constants.translateConstant]
  rfl

-- A marker consumes the same global index as symbols even on Driver; the
-- computed annotation list is not attached by upstream's constant branch.
example : (State.run (Constants.expression Target.pinnedApple Target.emptyEnvironment
    (literal [.marker 7])) context).2.freshness.next = 506 := by
  simp only [Constants.expression, literal, Constants.translateConstant]
  rfl
example : (State.run (Constants.expression Target.pinnedApple Target.emptyEnvironment
    (literal [.marker 7])) context).1 =
    .ok (.mk [.loc .unknown, .expr, .value (.integer (.signed .int))]
      (.pure (Constants.loadedInteger 42))) := by
  simp only [Constants.expression, literal, Constants.translateConstant]
  rfl

-- Pointer-null fast paths bypass annotations and marker validation/allocation.
private def nullExpression : Ail.TypedExpression := .mk
  (.rvalue (.pointer ⟨false, false, false⟩ (.mk [] .void)))
  [.marker 1, .marker 2] .unknown (.const .null)
private def nullType : Ctype :=
  .mk [.loc .unknown] (.pointer ⟨false, false, false⟩ (.mk [] .void))
example : State.run (Constants.expression Target.pinnedApple Target.emptyEnvironment nullExpression) context =
    (.ok (pureEffect (specified (nullptr nullType))), context) := by rfl

example : Constants.decodeCharacter Target.pinnedApple (.utf8 "A") = .ok 65 := by cbv
example : Constants.decodeCharacter Target.pinnedApple (.utf8 "\\n") = .ok 10 := by cbv
example : Constants.decodeCharacter Target.pinnedApple (.utf8 "\\377") = .ok (-1) := by cbv
example : Constants.decodeCharacter {Target.pinnedApple with plainCharSigned := false}
    (.utf8 "\\xFF") = .ok 255 := by cbv
-- Preserve upstream's octal-digit8 acceptance, without inventing C conformance.
example : Constants.decodeCharacter Target.pinnedApple (.utf8 "\\8") = .ok 8 := by cbv
example : (Constants.decodeCharacter Target.pinnedApple (.utf8 "\\?")).isOk = false := by cbv
example : Constants.concreteMaximum Target.pinnedApple Target.emptyEnvironment .bool = .ok 255 := rfl
example : Constants.concreteMaximum Target.pinnedApple Target.emptyEnvironment .wchar = .ok 4294967295 := rfl
example : Constants.concreteMinimum Target.pinnedApple Target.emptyEnvironment .wint = .ok 0 := rfl
example : (Constants.translateConstant Target.pinnedApple Target.emptyEnvironment
    (.floating ("1.0", none))).isOk = false := by simp only [Constants.translateConstant]; rfl

-- Aggregate constant translation recurses through actual Ail constants.
example : Constants.translateConstant Target.pinnedApple Target.emptyEnvironment
    (.array integerType [.integer (.iconstant 1 .decimal none), .predefined .false_]) =
    .ok (specified (array [Constants.loadedInteger 1, Constants.loadedInteger 0])) := by
  cbv

private def runtimeSymbol : Sym := ⟨⟨[]⟩, 5, .id "conv_loaded_int"⟩
private def runtime : List Runtime.Binding :=
  [(runtimeSymbol, .function (.loaded .integer) [] (Constants.loadedInteger 0))]
-- The actual runtime call retains the destination's source annotations.
example : Conversion.loadedArithmetic runtime integerType integerType (Constants.loadedInteger 42) =
    .ok (call (.sym runtimeSymbol) [ctype integerType, Constants.loadedInteger 42]) := rfl
example : (Conversion.loadedArithmetic [] integerType integerType (Constants.loadedInteger 42)).isOk = false := rfl
example : (Conversion.loadedArithmetic runtime integerType (.mk [] (.atomic integerType))
    (Constants.loadedInteger 42)).isOk = false := rfl

#print axioms Constants.translate_integer
#print axioms Constants.integer_expression_annotations
#print axioms Constants.pinned_hex_ff_character
#print axioms Conversion.loadedArithmetic_integer
