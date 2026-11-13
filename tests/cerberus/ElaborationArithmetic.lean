import Silmaril.Cerberus.Elaboration.Arithmetic.Thms
import Silmaril.Cerberus.Elaboration.Expressions.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Construction

-- The dispatcher uses a dependent node match; give cbv its kernel equation.
attribute [local cbv_eval] Expressions.expression.eq_def

private def context : State.Context := State.initial ⟨⟨[]⟩, 505, 1000⟩ .normal "Driver"
private def signedInt : Ctype := .mk [.loc .unknown] (.basic (.integer (.signed .int)))
private def literal (value : Int) (annotations : List Annot := []) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) annotations .unknown
    (.const (.integer (.iconstant value .decimal none)))
private def binary (operator : ArithmeticOperator) (left right : Ail.TypedExpression) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.binary left (.arithmetic operator) right)
private def convSymbol : Sym := ⟨⟨[]⟩, 5, .id "conv_int"⟩
private def reprSymbol : Sym := ⟨⟨[]⟩, 6, .id "all_values_representable_in"⟩
private def runtime : List Runtime.Binding :=
  [(convSymbol, .function (.object .integer) [] (integer 0)),
   (reprSymbol, .function .boolean [] (boolean true))]
private def result (input : Ail.TypedExpression) : Except State.Error Effect × State.Context :=
  State.run (Expressions.expression Target.pinnedApple Target.emptyEnvironment runtime input) context

-- The same marked child consumes its index after Add's five allocations but
-- before Mul/Sub's five allocations. Check the actual outer binder symbol.
private def firstSymbol : Pat → Option Nat
  | .mk _ (.base (some symbol, _)) => some symbol.number
  | .mk _ (.ctor .tuple (first :: _)) => match first with
      | .mk _ (.base (some symbol, _)) => some symbol.number
      | _ => none
  | _ => none
private def leadingBinder : Except State.Error Effect → Option Nat
  | .ok (.mk _ (.wseq pattern _ _)) => firstSymbol pattern
  | _ => none
example : leadingBinder (result (binary .add (literal 6 [.marker 9]) (literal 7))).1 = some 505 := by cbv
example : leadingBinder (result (binary .mul (literal 6 [.marker 9]) (literal 7))).1 = some 506 := by cbv
example : leadingBinder (result (binary .sub (literal 6 [.marker 9]) (literal 7))).1 = some 506 := by cbv
example : (result (binary .add (literal 6 [.marker 9]) (literal 7))).2.freshness.next = 511 := by cbv

-- The genuine arithmetic oracle has this actual expression shape; each binary
-- node consumes five symbols, preserving the unused capability temporary.
private def arithmetic : Ail.TypedExpression :=
  binary .sub (binary .mul (binary .add (literal 6) (literal 7)) (literal 3)) (literal 2)
-- Recursive alias plumbing increases kernel reduction depth on this nested tree.
set_option maxRecDepth 2048 in
example : (result arithmetic).1.isOk = true := by cbv
set_option maxRecDepth 2048 in
example : (result arithmetic).2.freshness.next = 520 := by cbv
example : (State.run (Expressions.expression Target.pinnedApple Target.emptyEnvironment []
    (binary .add (literal 6) (literal 7))) context).1.isOk = true := by cbv
example : (State.run (Expressions.expression Target.pinnedApple Target.emptyEnvironment []
    (binary .mul (literal 6) (literal 7))) context).1.isOk = false := by cbv
example : (result (binary .div (literal 6) (literal 7))).1.isOk = false := by cbv

-- Mixed-sign conversion retains the runtime representability test, the
-- promoted source annotations in that test, and both signed/unsigned branches.
private def signedLong : Ctype := .mk [.std "left"] (.basic (.integer (.signed .long)))
private def unsignedInt : Ctype := .mk [.std "right"] (.basic (.integer (.unsigned .int)))
private def representable : Pure := call (.sym reprSymbol) [ailCtype unsignedInt, ailCtype signedLong]
private def converted (type : IntegerType) (value : Int) : Pure :=
  call (.sym convSymbol) [ailCtype (.mk [] (.basic (.integer type))), integer value]
example : Arithmetic.usualArithmetic Target.pinnedApple Target.emptyEnvironment runtime false
    signedLong unsignedInt (integer 1) (integer 2) = .ok
    (ifPure representable (converted (.signed .long) 1) (converted (.unsigned .long) 1),
     ifPure representable (converted (.signed .long) 2) (converted (.unsigned .long) 2)) := by cbv

example : Arithmetic.withIntegerBehavior Target.pinnedApple Target.emptyEnvironment signedInt .add
    (integer 1) (integer 2) (integer 3) =
    .ok (catchExceptionalCondition (.signed .int) .add (integer 1) (integer 2)) := rfl
example : Arithmetic.withIntegerBehavior Target.pinnedApple Target.emptyEnvironment
    (.mk [] (.basic (.integer (.unsigned .int)))) .mul (integer 1) (integer 2) (integer 3) =
    .ok (wrapInteger (.unsigned .int) .mul (integer 1) (integer 2)) := rfl
example : (State.run (Expressions.expression {Target.pinnedApple with cheri := true}
    Target.emptyEnvironment runtime (binary .add (literal 6) (literal 7))) context).1.isOk = false := by cbv

#print axioms Arithmetic.usual_signed_int
#print axioms Arithmetic.signed_overflow
#print axioms Expressions.constant_dispatch
