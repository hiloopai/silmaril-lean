module

public import Silmaril.Compiler.Core.ElaborationTotal.Defs
public import Silmaril.Compiler.Core.Verified.CallArg.Defs
public import Silmaril.Compiler.Core.CalleeReturn.Defs

/-! Independently selected typed-Ail identity call with one real parameter
object. The explicit runtime covers only the equations used here; it is not a
pinned-runtime adequacy assumption. Execution claims use an existential actual
Core schedule, with no native, ABI, all-schedule or whole-C claim. -/
@[expose] public section
namespace Silmaril.Compiler.Core.ParameterCallReturn
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

namespace Example
def sym (index : Nat) (name : String) : Sym := ⟨⟨[]⟩, index, .id name⟩
def fSymbol := sym 1 "id"
def parameterSymbol := sym 21 "x"
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
def lengthTail := sym 35 "xs"
def nth := sym 36 "params_nth"
def nthList := sym 37 "cs_nth"
def nthIndex := sym 38 "n"
def nthHead := sym 39 "head"
def nthTail := sym 40 "tail"

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

/-- Explicit constructed runtime for singleton length, zero-index parameter
lookup and in-range integer conversion. Unused conversion/nth cases are explicit
zero/undefined branches; no full-runtime equivalence is claimed. -/
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
        [(.mk [] (.ctor (.nil .ctype) []), symbolPure accumulator),
         (.mk [] (.ctor .cons [wildcard .ctype, symbolPattern lengthTail (.list .ctype)]),
          call (.sym lengthAux)
            [operation .add (symbolPure accumulator) (integer 1), symbolPure lengthTail])])),
    (nth, .function .ctype [(nthList, .list .ctype), (nthIndex, .object .integer)]
      (casePure (symbolPure nthList)
        [(.mk [] (.ctor (.nil .ctype) []), undefined .unknown .UB038_number_of_args),
         (.mk [] (.ctor .cons [symbolPattern nthHead .ctype, symbolPattern nthTail (.list .ctype)]),
          ifPure (operation .eq (symbolPure nthIndex) (integer 0)) (symbolPure nthHead)
            (undefined .unknown .UB038_number_of_args))]))]
  impl := []
  aliases := []

def statement (node : Ail.StatementNode Ail.GenTypeCategory) : Ail.TypedStatement :=
  .mk .unknown ⟨false, none⟩ (.mk []) node
def integer42 : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant 42 .decimal none)))
def parameterExpression : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.rvalue (.mk (.lvalue qualifiers intType false) [] .unknown (.ident parameterSymbol)))
def fBody : Ail.TypedStatement :=
  statement (.block [] [statement (.return_ parameterExpression)])
def functionType : Ctype := .mk [] (.function (qualifiers, intType) [(qualifiers, (intType, false))] false)
def callExpression : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.call (.mk (.rvalue (.pointer qualifiers functionType)) [] .unknown (.functionDecay
      (.mk (.lvalue qualifiers functionType false) [] .unknown (.ident fSymbol)))) [integer42])
def mainBody : Ail.TypedStatement :=
  statement (.block [] [statement (.return_ callExpression)])

/-- Source syntax is chosen independently of compiler output or Core behavior:
`int id(int x) { return x; } int main(void) { return id(42); }`. -/
def program : Ail.TypedProgram :=
  (some mainSymbol, {
    declarations := [
      (fSymbol, .unknown, .mk [], .function true (qualifiers, intType) [(qualifiers, (intType, false))] false false false),
      (mainSymbol, .unknown, .mk [], .function true (qualifiers, intType) [] false false false)]
    objectDefinitions := []
    functionDefinitions := [
      (fSymbol, {loc := .unknown, marker := 7, attrs := .mk [], params := [parameterSymbol], body := fBody}),
      (mainSymbol, {loc := .unknown, marker := 8, attrs := .mk [], params := [], body := mainBody})]
    externIdmap := [(⟨.unknown, "id"⟩, fSymbol, .definition),
      (⟨.unknown, "main"⟩, mainSymbol, .definition)]
    staticAssertions := [], tagDefinitions := [], typedefAttributes := []
    loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := []
    cnDatatypes := [], cnDeclSpecs := [], cnIdents := [] })

def freshness : Freshness.Context := ⟨⟨[]⟩, 100, 1000⟩

/-- The actual explicit-input elaborator; no expected Core result is an input. -/
def elaborated := Functions.elaborate Silmaril.Cerberus.Target.pinnedApple
  Silmaril.Cerberus.Target.emptyEnvironment runtime program freshness
end Example
end Silmaril.Compiler.Core.ParameterCallReturn
