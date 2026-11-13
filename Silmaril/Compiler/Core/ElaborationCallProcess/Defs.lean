module

public import Silmaril.Compiler.Core.ElaborationTotal.Defs
public import Silmaril.Compiler.Core.CallReturn.Defs

/-! Independently selected typed-Ail source and explicit elaboration inputs for
one nonempty two-function call milestone. The runtime is constructed with the
recognizer-required empty-list and in-range conversion equations. It is not a
pinned runtime copy and supplies no whole-C, frontend or target adequacy claim. -/
@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationCallProcess
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

namespace Example
def sym (index : Nat) (name : String) : Sym := ⟨⟨[]⟩, index, .id name⟩
def fSymbol := sym 1 "f"
def mainSymbol := sym 20 "main"
def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
def qualifiers : Qualifiers := ⟨false, false, false⟩
def conversion := sym 2 "conv_loaded_int"
def convertInteger := sym 3 "conv_int"
def representable := sym 4 "is_representable_integer"
def typeParameter := sym 10 "type"
def valueParameter := sym 11 "value"
def numberParameter := sym 12 "number"
def length := sym 30 "params_length"
def lengthAux := sym 31 "params_length_aux"
def lengthParameter := sym 32 "cs"
def accumulator := sym 33 "acc"
def lengthList := sym 34 "cs_aux"

def representableBody : Pure :=
  operation .and
    (operation .le (ivmin (symbolPure typeParameter)) (symbolPure numberParameter))
    (operation .le (symbolPure numberParameter) (ivmax (symbolPure typeParameter)))
def convertIntegerBody : Pure :=
  ifPure (operation .eq (symbolPure typeParameter) (ctype (.mk [] (.basic (.integer .bool)))))
    (integer 0)
    (ifPure (call (.sym representable) [symbolPure numberParameter, symbolPure typeParameter])
      (symbolPure numberParameter) (integer 0))
def conversionBody : Pure :=
  casePure (symbolPure valueParameter)
    [(.mk [] (.ctor .specified [symbolPattern numberParameter (.object .integer)]),
      specified (call (.sym convertInteger) [symbolPure typeParameter, symbolPure numberParameter]))]

/-- Explicit constructed runtime, including the actual empty-parameter length
calculation used by this source. Runtime aliases are empty explicitly. -/
def runtime : Functions.RuntimeInputs where
  stdlib := [
    (conversion, .function (.loaded .integer)
      [(typeParameter, .ctype), (valueParameter, .loaded .integer)] conversionBody),
    (convertInteger, .function (.object .integer)
      [(typeParameter, .ctype), (numberParameter, .object .integer)] convertIntegerBody),
    (representable, .function .boolean
      [(numberParameter, .object .integer), (typeParameter, .ctype)] representableBody),
    (length, .function (.object .integer) [(lengthParameter, .list .ctype)]
      (call (.sym lengthAux) [integer 0, symbolPure lengthParameter])),
    (lengthAux, .function (.object .integer)
      [(accumulator, .object .integer), (lengthList, .list .ctype)]
      (casePure (symbolPure lengthList)
        [(.mk [] (.ctor (.nil .ctype) []), symbolPure accumulator)]))]
  impl := []
  aliases := []

def statement (node : Ail.StatementNode Ail.GenTypeCategory) : Ail.TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) node
def integer42 : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant 42 .decimal none)))
def fBody : Ail.TypedStatement :=
  statement (.block [] [statement (.return_ integer42)])
def functionType : Ctype := .mk [] (.function (qualifiers, intType) [] false)
def callExpression : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.call (.mk (.rvalue (.pointer qualifiers functionType)) [] .unknown (.functionDecay
      (.mk (.lvalue qualifiers functionType false) [] .unknown (.ident fSymbol)))) [])
def mainBody : Ail.TypedStatement :=
  statement (.block [] [statement (.return_ callExpression)])

/-- Source syntax is chosen independently of compiler output or Core behavior:
`int f(void) { return 42; } int main(void) { return f(); }`. -/
def program : Ail.TypedProgram :=
  (some mainSymbol, {
    declarations := [
      (fSymbol, .unknown, .mk [], .function true (qualifiers, intType) [] false false false),
      (mainSymbol, .unknown, .mk [], .function true (qualifiers, intType) [] false false false)]
    objectDefinitions := []
    functionDefinitions := [
      (fSymbol, {loc := .unknown, marker := 7, attrs := .mk [], params := [], body := fBody}),
      (mainSymbol, {loc := .unknown, marker := 8, attrs := .mk [], params := [], body := mainBody})]
    externIdmap := [(⟨.unknown, "f"⟩, fSymbol, .definition),
      (⟨.unknown, "main"⟩, mainSymbol, .definition)]
    staticAssertions := [], tagDefinitions := [], typedefAttributes := []
    loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := []
    cnDatatypes := [], cnDeclSpecs := [], cnIdents := [] })

def freshness : Freshness.Context := ⟨⟨[]⟩, 100, 1000⟩

/-- The actual explicit-input elaborator; no expected Core result is an input. -/
def elaborated := Functions.elaborate Silmaril.Cerberus.Target.pinnedApple
  Silmaril.Cerberus.Target.emptyEnvironment runtime program freshness
end Example
end Silmaril.Compiler.Core.ElaborationCallProcess
