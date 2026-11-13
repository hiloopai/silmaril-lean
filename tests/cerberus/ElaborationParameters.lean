import Silmaril.Cerberus.Elaboration.Functions.Defs

/-! Successful source equations for normal pointer formals only. These checks
construct actual Core syntax; they prove no independent Ail/native semantics. -/

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

namespace ElaborationParameterTests

private def symbol (number : Nat) (description : SymbolDescription := .none) : Sym :=
  ⟨⟨[]⟩, number, description⟩
private def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
private def plain : Qualifiers := ⟨false, false, false⟩
private def functionSymbol : Sym := symbol 1 (.id "f")
private def parameter : Sym := symbol 2 (.id "x")
private def secondParameter : Sym := symbol 3 (.id "y")
private def context : State.Context := State.initial ⟨⟨[4]⟩, 10, 100⟩ .normal "Driver"
private def body : Ail.TypedStatement := .mk .unknown ⟨false, none⟩ ⟨[]⟩
  (.return_ (.mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant 42 .decimal none)))))
private def definition (formals : List Sym) : Ail.FunctionDefinition Ail.GenTypeCategory where
  loc := .unknown
  marker := 0
  attrs := ⟨[]⟩
  params := formals
  body := body
private def declaration (count : Nat) : Ail.Declaration :=
  .function true (plain, intType) (List.replicate count (plain, intType, false)) false false false
private def program (formals : List Sym) : Ail.TypedProgram := (none, {
  declarations := [(functionSymbol, .unknown, ⟨[]⟩, declaration formals.length)]
  objectDefinitions := []
  functionDefinitions := [(functionSymbol, definition formals)]
  staticAssertions := [], tagDefinitions := [], externIdmap := [], typedefAttributes := []
  loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := [], cnDatatypes := []
  cnDeclSpecs := [], cnIdents := []})
-- Elaboration only needs a named pure conversion binding here. Its correctness
-- and runtime recognition are deliberately not asserted by these source tests.
private def runtime : Functions.RuntimeInputs := {
  stdlib := [(symbol 90 (.id "conv_loaded_int"),
    .function (.loaded .integer) [(symbol 91, .ctype), (symbol 92, .loaded .integer)]
      (symbolPure (symbol 92)))]
  impl := [], aliases := []}
private def one := State.run
  (Functions.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime (program [parameter]) {}
    (functionSymbol, .unknown, ⟨[]⟩, declaration 1)) context
private def two := State.run
  (Functions.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime (program [parameter, secondParameter]) {}
    (functionSymbol, .unknown, ⟨[]⟩, declaration 2)) context
private def formals : FunDecl Codec.wireModel Unit Unit → List (Sym × BaseType)
  | .procedure _ _ _ inputs _ => inputs
  | _ => []

-- The generated wrappers consume IDs but do not become procedure formals.
example : (State.run (Functions.reserveParameterSymbols [parameter, secondParameter]
    [.object .pointer, .object .pointer]) context).2.freshness.next = 12 := by cbv
theorem one_formals : one.1.toOption.map (fun output => output.functions.map (fun pair => formals pair.2)) =
    some [[(parameter, .object .pointer)]] := by cbv
example : two.1.toOption.map (fun output => output.functions.map (fun pair => formals pair.2)) =
    some [[(parameter, .object .pointer), (secondParameter, .object .pointer)]] := by cbv
-- Metadata retains original symbols and declared Ctypes in their source order.
theorem one_metadata : one.1.toOption.map (fun output => output.info.map (fun pair => pair.2.2.2.2.1)) =
    some [[(some parameter, intType)]] := by cbv
-- One unused wrapper, return label, body return temporary and default binder.
theorem one_freshness : one.2.freshness.next = 14 := by cbv
example : two.2.freshness.next = 15 := by cbv
-- Caller-owned formals are absent from the callee's local-object scope/type map.
example : one.2.effects.visibleObjects = context.effects.visibleObjects := by cbv
example : one.2.effects.visibleObjectTypes = context.effects.visibleObjectTypes := by cbv
-- Reject malformed input before allocating IDs; this is an explicit local
-- successful-equation domain restriction, rather than an upstream failure match.
private def mismatched := State.run
  (Functions.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime (program []) {}
    (functionSymbol, .unknown, ⟨[]⟩, declaration 1)) context
theorem mismatched_formals : mismatched.1 = .error (.message "defined-function declared/defined parameter counts differ") := rfl
example : mismatched.2 = context := rfl

-- Qualifiers do not introduce a callee parameter scope or const-alias IDs in
-- the normal convention. The metadata keeps distinct Ctypes in source order.
private def longType : Ctype := .mk [] (.basic (.integer (.signed .long)))
private def mixedDeclaration : Ail.Declaration :=
  .function true (plain, intType)
    [(⟨true, false, false⟩, intType, false), (plain, longType, true)] false false false
private def mixedProgram : Ail.TypedProgram :=
  (none, {(program [parameter, secondParameter]).2 with
    declarations := [(functionSymbol, .unknown, ⟨[]⟩, mixedDeclaration)]})
private def mixed := State.run
  (Functions.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime mixedProgram {}
    (functionSymbol, .unknown, ⟨[]⟩, mixedDeclaration)) context
theorem mixed_metadata : mixed.1.toOption.map
    (fun output => output.info.map (fun pair => pair.2.2.2.2.1)) =
      some [[(some parameter, intType), (some secondParameter, longType)]] := by cbv
example : mixed.2.freshness.next = 15 := by cbv
example : mixed.2.effects.visibleObjects = context.effects.visibleObjects := by cbv
example : mixed.2.effects.visibleObjectTypes = context.effects.visibleObjectTypes := by cbv

private def returnBinding : FunDecl Codec.wireModel Unit Unit → Option (Nat × Nat)
  | .procedure _ _ _ _ (.mk _ (.sseq _ _ (.mk _ (.save (label, _) [(temporary, _)] _)))) =>
      some (label.number, temporary.number)
  | _ => none
-- The reserved argument wrapper precedes the actual return label, and the
-- fallback result binder is still allocated after body translation.
theorem one_return_allocation : one.1.toOption.map
    (fun output => output.functions.map (fun pair => returnBinding pair.2)) =
      some [some (11, 13)] := by cbv
example : two.1.toOption.map
    (fun output => output.functions.map (fun pair => returnBinding pair.2)) =
      some [some (12, 14)] := by cbv

#print axioms Functions.reserveParameterSymbols
#print axioms one_formals
#print axioms one_metadata
#print axioms one_freshness
#print axioms mixed_metadata
#print axioms one_return_allocation
#print axioms mismatched_formals

end ElaborationParameterTests
