import Silmaril.Cerberus.Elaboration.Comparisons.Thms
import Silmaril.Cerberus.Elaboration.ControlTests.Thms

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Construction

private def context : State.Context := State.initial ⟨⟨[]⟩, 100, 1000⟩ .normal "Driver"
private def leftType : Ctype := .mk [.std "left type"] (.basic (.integer (.signed .int)))
private def rightType : Ctype := .mk [.std "right type"] (.basic (.integer (.signed .int)))
private def resultType : Ctype := .mk [.loc (.point "comparison.c" 2 4)] (.basic (.integer (.signed .int)))
private def convSymbol : Sym := ⟨⟨[]⟩, 5, .id "conv_int"⟩
private def runtime : List Runtime.Binding :=
  [(convSymbol, .function (.object .integer) [] (integer 0))]
private def marked : State.ElabM Effect := do
  let _ ← State.recordObjectTypesMarker
  return pureEffect (Constants.loadedInteger 7)
private def right : State.ElabM Effect := pure (pureEffect (Constants.loadedInteger 3))
private def greater := State.run (Comparisons.greater Target.pinnedApple Target.emptyEnvironment
  runtime resultType leftType rightType marked right) context
private def equal := State.run (Comparisons.equal Target.pinnedApple Target.emptyEnvironment
  runtime resultType leftType rightType marked right) context

private def firstSymbol : Pat → Option Nat
  | .mk _ (.ctor .tuple (.mk _ (.base (some symbol, _)) :: _)) => some symbol.number
  | _ => none
private def leadingBinder : Except State.Error Effect → Option Nat
  | .ok (.mk _ (.wseq pattern _ _)) => firstSymbol pattern
  | _ => none
private def annotations : Except State.Error Effect → Option (List Annot)
  | .ok (.mk annotations _) => some annotations
  | _ => none
private def fallback : Except State.Error Effect → Option Pure
  | .ok (.mk _ (.wseq _ _ (.mk _ node))) => match node with
      | .case_ _ [_, (_, .mk _ (.pure value))] => some value
      | .pure (.mk _ _ (.case_ _ [_, (_, value)])) => some value
      | _ => none
  | _ => none
private def relationalBranch : Except State.Error Effect → Option (List Annot × Pure)
  | .ok (.mk _ (.wseq _ _ (.mk _ node))) => match node with
      | .case_ _ ((_, .mk annotations (.pure value)) :: _) => some (annotations, value)
      | _ => none
  | _ => none
private def equalityBranch : Except State.Error Effect → Option Pure
  | .ok (.mk _ (.wseq _ _ (.mk _ node))) => match node with
      | .pure (.mk _ _ (.case_ _ ((_, value) :: _))) => some value
      | _ => none
  | _ => none

-- These observations distinguish child-before-allocation Gt from
-- allocation-before-child Eq, and count the unused fifth Boolean wrapper.
example : leadingBinder greater.1 = some 101 := by cbv
example : leadingBinder equal.1 = some 100 := by cbv
example : greater.2.freshness.next = 106 := by cbv
example : equal.2.freshness.next = 106 := by cbv
example : annotations greater.1 = some [.std "§6.5.8"] := by cbv
example : annotations equal.1 = some [] := by cbv
example : fallback greater.1 = some (unspecified resultType) := by cbv
example : fallback equal.1 = some (unspecified resultType) := by cbv

private def converted (index : Nat) : Pure := call (.sym convSymbol)
  [ailCtype (.mk [] (.basic (.integer (.signed .int)))), symbolPure ⟨⟨[]⟩, index, .none⟩]
-- Inspect the actual specified branch, including its source standard tags,
-- runtime conversions, symbol indices and specified object integers 1/0.
example : relationalBranch greater.1 = some
    ([.std "§6.5.8#6"], ifPure (operation .gt
      (standardPure "§6.5.8#3" (converted 103))
      (standardPure "§6.5.8#3" (converted 104)))
      (specified (integer 1)) (specified (integer 0))) := by cbv
example : equalityBranch equal.1 = some
    (standardPure "§6.5.9#3" (ifPure
      (standardPure "§6.5.9#4, sentence 3" (operation .eq
        (standardPure "§6.5.9#4, sentence 1" (converted 102))
        (standardPure "§6.5.9#4, sentence 1" (converted 103))))
      (specified (integer 1)) (specified (integer 0)))) := by cbv

-- Scalar helpers do not silently choose direct conversion or pointer rules.
example : (State.run (Comparisons.greater Target.pinnedApple Target.emptyEnvironment []
    resultType leftType rightType marked right) context).1.isOk = false := by cbv
example : (State.run (Comparisons.equal Target.pinnedApple Target.emptyEnvironment runtime
    resultType (.mk [] (.pointer ⟨false, false, false⟩ (.mk [] .void))) rightType marked right)
    context).1.isOk = false := by cbv
example : (State.run (Comparisons.equal {Target.pinnedApple with cheri := true}
    Target.emptyEnvironment runtime resultType leftType rightType marked right) context).1.isOk = false := by cbv

-- The test result category is signed int. The zero child retains the input's
-- unsigned category and actual annotations/location, with octal spelling.
private def location : Loc := .region "control-flow.c" 1 33 "control-flow.c" 1 38
private def category : Ail.GenTypeCategory := .rvalue (.basic (.integer (.concrete (.unsigned .int))))
private def input : Ail.TypedExpression := .mk category [.marker 7, .std "original"] location
  (.const (.integer (.iconstant 7 .decimal none)))
example : ControlTests.equalZero Target.pinnedApple Target.emptyEnvironment input = .ok
    (.mk ControlTests.signedIntCategory [.marker 7, .std "original"] location
      (.binary input .eq (.mk category [.marker 7, .std "original"] location
        (.const (.integer (.iconstant 0 .octal none)))))) := by cbv
example : (ControlTests.equalZero Target.pinnedApple Target.emptyEnvironment
    (.mk (.rvalue (.pointer ⟨false, false, false⟩ (.mk [] .void))) [] location (.const .null))).isOk = false := by cbv

#print axioms Comparisons.booleanInteger_shape
#print axioms Comparisons.specifiedPair_shape
#print axioms ControlTests.equalZero_integer
