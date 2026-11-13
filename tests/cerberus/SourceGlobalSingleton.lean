import Silmaril.Cerberus.Elaboration.Functions.Defs

/-! Actual source-global kernel checks. The only construction inputs are typed
Ail, explicit target/type/runtime bindings and the supplied fresh history.
Expected Core appears only on theorem right-hand sides. The named conversion
binding tests lookup/construction, without asserting its runtime semantics. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction
namespace SourceGlobalSingletonTests
def mainSymbol : Sym := ⟨⟨[]⟩, 0, .id "main"⟩
def globalSymbol : Sym := ⟨⟨[]⟩, 1, .id "g"⟩
def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
def integer (number : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant number .decimal none)))
def definition : Ail.FunctionDefinition Ail.GenTypeCategory where
  loc := .unknown
  marker := 0
  attrs := ⟨[]⟩
  params := []
  body := .mk .unknown ⟨false, none⟩ ⟨[]⟩ (.return_ (integer 42))
def program : Ail.TypedProgram := (some mainSymbol, {
  declarations := [(mainSymbol, .unknown, ⟨[]⟩,
    .function true (⟨false,false,false⟩, intType) [] false false false),
    (globalSymbol, .unknown, ⟨[]⟩,
    .object (.static, false) none ⟨false,false,false⟩ intType)]
  objectDefinitions := [(globalSymbol, integer 0)]
  functionDefinitions := [(mainSymbol, definition)]
  staticAssertions := [], tagDefinitions := []
  externIdmap := [(⟨.unknown, "main"⟩, mainSymbol, .definition),
    (⟨.unknown, "g"⟩, globalSymbol, .definition)]
  typedefAttributes := []
  loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := [], cnDatatypes := []
  cnDeclSpecs := [], cnIdents := []})

def conversion : Sym := ⟨⟨[4]⟩, 90, .id "conv_loaded_int"⟩
def conversionArgument : Sym := ⟨⟨[4]⟩, 91, .none⟩
def runtime : Functions.RuntimeInputs := {
  stdlib := [(conversion, .function (.loaded .integer)
    [(conversionArgument, .loaded .integer)] (symbolPure conversionArgument))]
  impl := [], aliases := []}
def freshness : Freshness.Context := ⟨⟨[4]⟩, 10, 100⟩
def output := Functions.elaborate Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime program freshness

theorem actual_global_source_accepts :
    output.1.toOption.map (fun file => (file.globs.length, file.funs.length)) = some (1,1) := by cbv

theorem source_freshness : output.2.freshness = {freshness with next := 15} := by cbv

def fresh (index : Nat) : Sym := ⟨freshness.digest, index, .none⟩
def expectedGlobal (location : Loc) (alignment : Pure) (qualifiers : Qualifiers)
    (input : Ail.TypedExpression) (resultIndex : Nat) : Global Codec.wireModel Unit Unit :=
  .definition (.object .pointer, intType) (addLocation .unknown
    (strongSequence (symbolPattern (fresh 10) (.object .pointer))
      (MemoryActions.create location alignment
        (ailCtype intType) (.source location [globalSymbol]))
      (strongSequence (symbolPattern (fresh resultIndex) (.loaded .integer))
        (.mk [.std "§6.5#2"] (.bound
          (addLocation (match input with | .mk _ _ location _ => location)
            (addExpression (Constants.annotateIntegerEffect intType
              (pureEffect (Constants.loadedInteger 0)))))))
        (strongSequence (wildcard .unit)
          (MemoryActions.store location qualifiers.const (ailCtype intType) (symbolPure (fresh 10))
            (call (.sym conversion) [ailCtype intType, symbolPure (fresh resultIndex)]) .na)
          (pureEffect (symbolPure (fresh 10)))))))

theorem actual_global_core : output.1.toOption.map (fun file => file.globs) =
    some [(globalSymbol, expectedGlobal .unknown (alignof (ailCtype intType)) ⟨false,false,false⟩ (integer 0) 11)] := by cbv

def markedInput : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [.marker 7]
    (.point "global.c" 2 3) (.const (.integer (.iconstant 0 .decimal none)))
def markedOutput := State.run
  (Globals.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime.stdlib [(globalSymbol,markedInput)]
    globalSymbol (.point "global.c" 1 1) ⟨[]⟩ (some (.integer 16)) ⟨true,false,false⟩ intType)
  (State.initial freshness .normal "Driver")

theorem marked_constant_freshness : markedOutput.2.freshness.next = 13 := by cbv

theorem marked_constant_core : markedOutput.1 =
    .ok (expectedGlobal (.point "global.c" 1 1) (Construction.integer 16)
      ⟨true,false,false⟩ markedInput 12) := by cbv

def externalOutput := State.run
  (Globals.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ [] [] globalSymbol
    .unknown ⟨[]⟩ none ⟨false,false,false⟩ intType)
  (State.initial freshness .normal "Driver")
theorem external_declaration_core : externalOutput.1 = .ok (.declaration (.object .pointer,intType)) := by cbv
theorem external_declaration_consumes_id : externalOutput.2.freshness.next = 11 := by cbv

theorem missing_runtime_rejects :
    (Functions.elaborate Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ {runtime with stdlib := []}
      program freshness).1 = .error (.message
        "[Translate_effect.E.mk_stdcall] `conv_loaded_int' is not a Core standard function.") := by cbv

def twoObjects : Ail.TypedProgram := (program.1, {program.2 with
  declarations := program.2.declarations ++ [(fresh 55,.unknown,⟨[]⟩,
    .object (.static,false) none ⟨false,false,false⟩ intType)]})
theorem multiple_objects_accept :
    (Functions.elaborate Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime twoObjects freshness).1.toOption.map
      (fun file => file.globs.length) = some 2 := by cbv

theorem nonconstant_global_reject :
    (State.run
      (Globals.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime.stdlib
        [(globalSymbol,.mk (.lvalue ⟨false,false,false⟩ intType false)
          [] .unknown (.ident globalSymbol))]
        globalSymbol .unknown ⟨[]⟩ none ⟨false,false,false⟩ intType)
      (State.initial freshness .normal "Driver")).1 =
      .error (.message "unsupported: global initializer is not a constant expression") := by cbv

def initializer : Global Codec.wireModel Unit Unit → Option Effect
  | .definition _ (.mk _ (.sseq _ _ (.mk _ (.sseq _ input _)))) => some input
  | _ => none
def literal : Effect → Option Int
  | .mk _ (.bound (.mk _ (.pure (.mk _ _ (.val (.loaded (.specified (.integer number)))))))) => some number
  | _ => none

def unsignedMaximum : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.unsigned .int))))) [] .unknown
    (.const (.integer (.max (.unsigned .int))))
def twoByteInt : Silmaril.Cerberus.Target.Config := {Silmaril.Cerberus.Target.pinnedApple with
  baseLayout := fun base => if base = .int then some ⟨2,2⟩
    else Silmaril.Cerberus.Target.pinnedApple.baseLayout base}
def targetMaximum (config : Silmaril.Cerberus.Target.Config) :=
  (State.run
    (Globals.declaration config ⟨∅⟩ runtime.stdlib [(globalSymbol,unsignedMaximum)]
      globalSymbol .unknown ⟨[]⟩ none ⟨false,false,false⟩ intType)
    (State.initial freshness .normal "Driver")).1.toOption.bind fun global =>
      (initializer global).bind literal

theorem target_is_supplied : targetMaximum twoByteInt = some 65535 := by cbv
theorem pinned_target_is_supplied : targetMaximum Silmaril.Cerberus.Target.pinnedApple = some 4294967295 := by cbv


def enumTag : Sym := ⟨⟨[4]⟩, 95, .id "enum e"⟩
def enumMaximum : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.enum enumTag))))) [] .unknown
    (.const (.integer (.max (.enum enumTag))))
def enumEnvironment : Silmaril.Cerberus.Target.Environment :=
  ⟨Map.insert enumTag (.unsigned .short) ∅⟩
theorem enum_environment_is_supplied :
  ((State.run
    (Globals.declaration Silmaril.Cerberus.Target.pinnedApple enumEnvironment runtime.stdlib
      [(globalSymbol,enumMaximum)] globalSymbol .unknown ⟨[]⟩ none ⟨false,false,false⟩ intType)
    (State.initial freshness .normal "Driver")).1.toOption.bind fun global =>
      (initializer global).bind literal) = some 65535 := by cbv

def longType : Ctype := .mk [] (.basic (.integer (.signed .long)))
theorem alignment_type_is_retained :
  (State.run
    (Globals.declaration Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime.stdlib
      [(globalSymbol,integer 0)] globalSymbol .unknown ⟨[]⟩ (some (.ctype longType))
      ⟨false,false,false⟩ intType)
    (State.initial freshness .normal "Driver")).1 =
    .ok (expectedGlobal .unknown (alignof (ailCtype longType)) ⟨false,false,false⟩ (integer 0) 11) := by cbv


#print axioms Globals.declaration
#print axioms actual_global_source_accepts
#print axioms actual_global_core
#print axioms source_freshness
#print axioms marked_constant_core
#print axioms marked_constant_freshness
#print axioms external_declaration_core
#print axioms external_declaration_consumes_id
#print axioms missing_runtime_rejects
#print axioms multiple_objects_accept
#print axioms nonconstant_global_reject
#print axioms target_is_supplied
#print axioms pinned_target_is_supplied
#print axioms enum_environment_is_supplied
#print axioms alignment_type_is_retained
end SourceGlobalSingletonTests
