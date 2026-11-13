import Silmaril.Cerberus.Elaboration.Functions.Defs
import Silmaril.Cerberus.Elaboration.CallArguments.Thms

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace ElaborationCallTests
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

attribute [local cbv_eval] Expressions.expression.eq_def

private def symbol (number : Nat) (description : SymbolDescription := .none) : Sym :=
  ⟨⟨[]⟩, number, description⟩
private def qualifiers : Qualifiers := ⟨false, false, false⟩
private def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def functionType (parameters : List (Qualifiers × Ctype × Bool) := [])
    (variadic : Bool := false) : Ctype :=
  .mk [] (.function (qualifiers, intType) parameters variadic)
private def designator (type : Ctype := functionType) : Ail.TypedExpression :=
  .mk (.rvalue (.pointer qualifiers type)) [] .unknown (.functionDecay
    (.mk (.lvalue qualifiers type false) [] .unknown (.ident (symbol 1 (.id "f")))))
private def callExpression (annotations : List Annot := [])
    (parameters : List (Qualifiers × Ctype × Bool) := []) (variadic : Bool := false) :
    Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) annotations .unknown
    (.call (designator (functionType parameters variadic)) [])
-- Syntax-construction input only: this stub is never Core-evaluated below.
private def runtime : List Runtime.Binding :=
  [(symbol 2 (.id "params_length"), .function (.object .integer) [] (integer 0)),
    (symbol 4 (.id "params_nth"), .function .ctype [] (ailCtype intType)),
    (symbol 5 (.id "conv_loaded_int"), .function (.loaded .integer) [] (specified (integer 0)))]
private def aliases : Designators.Aliases := [("f", symbol 3 (.id "resolved_f"))]
private def context : State.Context := State.initial ⟨⟨[]⟩, 10, 1000⟩ .normal "Driver"
private def translate (input : Ail.TypedExpression) :=
  State.run (Expressions.expression Silmaril.Cerberus.Target.pinnedApple
    Silmaril.Cerberus.Target.emptyEnvironment runtime input aliases) context

/-- Inspect the actual designator child of the generated call, retaining the
loaded/specification wrappers required by Core procedure dispatch. -/
private def target : Effect → Option Sym
  | .mk _ (.sseq _ (.mk _ (.pure (.mk _ () (.val
      (.loaded (.specified (.pointer (.function symbol)))))))) _) => some symbol
  | _ => none

/-- The source call annotations are attached to the real Core call, after the
metadata checks and outside the recursive child translation. -/
private def callAnnotations : Effect → Option (List Annot)
  | .mk _ (.sseq _ _ (.mk _ (.let_ _ _ (.mk _ (.if_ _
      (.mk _ (.if_ _ (.mk annotations (.ccall () _ _ [])) _)) _))))) => some annotations
  | _ => none

private def binderNumbers : Effect → Option (Nat × Nat × Nat)
  | .mk _ (.sseq (.mk _ (.base (some function, .loaded .pointer))) _
      (.mk _ (.let_ (.mk _ (.ctor .tuple
        [.mk _ (.base (some result, .ctype)), .mk _ (.base (some parameters, .list .ctype)),
          .mk _ (.base (none, .boolean)), .mk _ (.base (none, .boolean))])) _ _))) =>
      some (function.number, result.number, parameters.number)
  | _ => none

theorem direct_alias : (translate (callExpression)).1.toOption.bind target =
    some (symbol 3 (.id "resolved_f")) := by cbv

theorem original_symbol : Designators.resolveAlias [] (symbol 1 (.id "f")) =
    symbol 1 (.id "f") := rfl
example : Designators.resolveAlias aliases (symbol 1 (.objectAddress "f")) =
    symbol 1 (.objectAddress "f") := by cbv
example : Designators.resolveAlias [("f", symbol 3), ("f", symbol 4)]
    (symbol 1 (.id "f")) = symbol 3 := by cbv

theorem three_wrappers : (translate (callExpression)).1.toOption.bind binderNumbers =
    some (10, 11, 12) ∧ (translate (callExpression)).2.freshness.next = 13 := by cbv

theorem marker_annotations :
    (translate (callExpression [.std "source", .marker 7])).1.toOption.bind callAnnotations =
      some [.markerObjectTypes 10, .std "source", .marker 7] ∧
    (translate (callExpression [.std "source", .marker 7])).1.toOption.bind binderNumbers =
      some (11, 12, 13) ∧
    (translate (callExpression [.std "source", .marker 7])).2.freshness.next = 14 := by cbv

theorem invalid_empty_arity :
    (translate (callExpression [] [(qualifiers, intType, false)])).1.toOption = none ∧
    (translate (callExpression [] [(qualifiers, intType, false)])).2.freshness.next = 10 := by cbv
example : (translate (callExpression [] [] true)).1.toOption = none := by cbv

private def oneArgument : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.call (designator (functionType [(qualifiers, intType, false)]))
      [.mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
        (.const (.integer (.iconstant 42 .decimal none)))])
theorem nonempty_accepts : (translate oneArgument).1.isOk = true ∧
    (translate oneArgument).2.freshness.next = 21 := by cbv

private def constant (value : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant value .decimal none)))
private def applied (arguments : List Ail.TypedExpression) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.call (designator (functionType (arguments.map fun _ => (qualifiers, intType, false)))) arguments)
private def nested := applied [applied [constant 20], applied [constant 22]]

/-- No desired Core body or execution result is supplied to this computation. -/
theorem recursive_arguments_accept : (translate nested).1.isOk = true ∧
    (translate nested).2.freshness.next = 47 := by cbv

private def afterChecks : Effect → Option Effect
  | .mk _ (.sseq _ (.mk _ (.unseq _))
      (.mk _ (.if_ _ _ (.mk _ (.if_ _ _ prepared))))) => some prepared
  | _ => none
private def createdNames : Effect → List Nat
  | .mk _ (.sseq (.mk _ (.base (some pointer, .object .pointer))) _ rest) =>
      pointer.number :: createdNames rest
  | _ => []
private def argumentChildren : Effect → List Effect
  | .mk _ (.sseq _ (.mk _ (.unseq (_ :: arguments))) _) => arguments
  | _ => []
private def preparationNames (core : Effect) : List Nat :=
  (afterChecks core).map createdNames |>.getD []

/-- All outer argument object symbols precede either nested call's symbols.
Runtime evaluation remains an actual unsequenced list of recursive children. -/
theorem object_names_before_recursive_children :
    (translate nested).1.toOption.map preparationNames = some [17,16] ∧
    (translate nested).1.toOption.map (fun core =>
      (argumentChildren core).map preparationNames) = some [[25],[37]] := by cbv

/-- Each parameter creation contains actual create/store with the expected CType,
false locking and NA order, under the exact source standard annotation. -/
private def storage (core : Effect) : Option (Nat × Prefix × Ctype) := do
  let .mk _ (.let_ _ _ (.mk _ (.if_ _ _ body))) := core | none
  let .mk [.std "§6.5.2.2#7, sentence 1"]
    (.wseq (.mk _ (.base (some pointer, .object .pointer))) created rest) := body | none
  let .mk _ (.action (.mk .pos (.mk _ ()
    (.create _ (.mk _ () (.val (.ctype type))) allocationPrefix)))) := created | none
  let .mk _ (.wseq _ stored returned) := rest | none
  let .mk _ (.action (.mk .pos (.mk _ ()
    (.store false (.mk _ () (.val (.ctype storedType))) (.mk _ () (.sym storedPointer))
      (.mk _ () (.call (.sym conversion)
        [.mk _ () (.val (.ctype convertedType)), .mk _ () (.sym _)])) .na)))) := stored | none
  let .mk _ (.pure (.mk _ () (.sym returnedPointer))) := returned | none
  if pointer.key == storedPointer.key && pointer.key == returnedPointer.key &&
      decide (storedType = type) && decide (convertedType = type) &&
      Runtime.hasName "conv_loaded_int" conversion then
    some (pointer.number, allocationPrefix, type) else none
private def storageObjects : Effect → List (Option (Nat × Prefix × Ctype))
  | .mk _ (.sseq (.mk _ (.base (some _, .object .pointer))) creation rest) =>
      storage creation :: storageObjects rest
  | _ => []
private def storedObjects (core : Effect) : List (Option (Nat × Prefix × Ctype)) :=
  ((afterChecks core).map storageObjects).getD []

/-- Prefix indices use call locations and the supplied digest; complete CType
locations from typed Ail are retained rather than synthesized from base types. -/
theorem actual_parameter_objects :
    (translate (applied [constant 20, constant 22])).1.toOption.map storedObjects =
      some [some (21, .funArg .unknown ⟨[]⟩ 0, .mk [] (.basic (.integer (.signed .int)))) ,
        some (23, .funArg .unknown ⟨[]⟩ 1, .mk [] (.basic (.integer (.signed .int))))] := by cbv

private def afterPreparation : Effect → Option Effect
  | .mk _ (.sseq (.mk _ (.base (some _, .object .pointer))) _ rest) =>
      afterPreparation rest
  | core => some core
private def pointerNumber : Pure → Option Nat
  | .mk _ () (.sym pointer) => some pointer.number
  | _ => none
private def killNumber : Effect → Option Nat
  | .mk _ (.action (.mk .pos (.mk _ () (.kill (.static _) pointer)))) => pointerNumber pointer
  | _ => none
private def actualCallLifetime (core : Effect) : Option (List Nat × List Nat × Pat) := do
  let prepared ← afterChecks core >>= afterPreparation
  let .mk _ (.sseq (.mk _ (.base (some result, .loaded .integer)))
    (.mk _ (.ccall () _ _ arguments))
    (.mk _ (.sseq killsPattern kills (.mk _ (.pure (.mk _ () (.sym returned))))))) := prepared | none
  let arguments ← arguments.mapM pointerNumber
  let .mk _ (.unseq actions) := kills | none
  let killed ← actions.mapM killNumber
  if result.key == returned.key then some (arguments, killed, killsPattern) else none

/-- The actual ccall consumes the same caller-owned object pointers that are
killed afterwards. Its bound loaded result is returned only after that cleanup. -/
theorem actual_call_and_cleanup :
    (translate (applied [constant 20, constant 22])).1.toOption.bind actualCallLifetime =
      some ([17,16], [17,16], wildcard (.tuple [.unit,.unit])) := by cbv

/-- Exhaustion on the last creation wrapper precedes the call-result allocation. -/
theorem parameter_wrapper_exhausts :
    (State.run (Expressions.expression Silmaril.Cerberus.Target.pinnedApple
      Silmaril.Cerberus.Target.emptyEnvironment runtime oneArgument aliases)
      (State.initial ⟨⟨[]⟩, 10, 18⟩ .normal "Driver")).1 =
        .error (.freshness .exhausted) ∧
    (State.run (Expressions.expression Silmaril.Cerberus.Target.pinnedApple
      Silmaril.Cerberus.Target.emptyEnvironment runtime oneArgument aliases)
      (State.initial ⟨⟨[]⟩, 10, 18⟩ .normal "Driver")).2.freshness.next = 19 := by cbv

#print axioms Designators.resolveAlias
#print axioms Calls.zeroArguments
#print axioms direct_alias
#print axioms three_wrappers
#print axioms marker_annotations
#print axioms invalid_empty_arity
#print axioms nonempty_accepts
#print axioms recursive_arguments_accept
#print axioms object_names_before_recursive_children
#print axioms actual_parameter_objects
#print axioms parameter_wrapper_exhausts
#print axioms actual_call_and_cleanup
#print axioms CallArguments.translate
#print axioms CallArguments.createParameter
#print axioms CallArguments.cleanup_one
#print axioms CallArguments.cleanup_pair

end ElaborationCallTests
