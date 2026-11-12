import Silmaril.Cerberus.Elaboration.Functions.Defs
import Init.Data.List.Sort.Lemmas

/-! Checks actual multiple-global source elaboration and the selected independent
ordering stage. No expected global/function bodies are elaborator inputs. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction
namespace SourceGlobalIndependentTests

def symbol (digest : List UInt8) (number : Nat) (name : String) : Sym :=
  ⟨⟨digest⟩,number,.id name⟩
def gX := symbol [2] 4 "x"
def gY := symbol [] 90 "y"
def gZ := symbol [] 3 "z"
def mainSymbol := symbol [] 0 "main"
def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
def integer (number : Int) : Ail.TypedExpression :=
  .mk (.rvalue (.basic (.integer (.concrete (.signed .int))))) [] .unknown
    (.const (.integer (.iconstant number .decimal none)))
def object (symbol : Sym) : Sym × (Loc × Attributes × Ail.Declaration) :=
  (symbol,.unknown,⟨[]⟩,.object (.static,false) none ⟨false,false,false⟩ intType)
def definition : Ail.FunctionDefinition Ail.GenTypeCategory where
  loc := .unknown
  marker := 0
  attrs := ⟨[]⟩
  params := []
  body := .mk .unknown ⟨false,none⟩ ⟨[]⟩ (.return_ (integer 42))
def program : Ail.TypedProgram := (some mainSymbol, {
  declarations := [object gY,object gX,object gZ,
    (mainSymbol,.unknown,⟨[]⟩,.function true (⟨false,false,false⟩,intType) [] false false false)]
  objectDefinitions := [(gX,integer 1),(gY,integer 2),(gZ,integer 3)]
  functionDefinitions := [(mainSymbol,definition)]
  staticAssertions := [], tagDefinitions := [], externIdmap := [], typedefAttributes := []
  loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := [], cnDatatypes := []
  cnDeclSpecs := [], cnIdents := []})
def conversion := symbol [9] 90 "conv_loaded_int"
def arg := symbol [9] 91 "arg"
def runtime : Functions.RuntimeInputs := {
  stdlib := [(conversion,.function (.loaded .integer) [(arg,.loaded .integer)] (symbolPure arg))]
  impl := [],aliases := []}
def freshness : Freshness.Context := ⟨⟨[4]⟩,10,100⟩
def output := Functions.elaborate Silmaril.Cerberus.Target.pinnedApple ⟨∅⟩ runtime program freshness

theorem actual_three_global_order : output.1.toOption.map (fun file => file.globs.map Prod.fst) =
    some [gZ,gY,gX] := by cbv

def binders : Global Codec.wireModel Unit Unit → Option (Nat × Nat)
  | .definition _ (.mk _ (.sseq (.mk _ (.base (some pointer,_))) _
      (.mk _ (.sseq (.mk _ (.base (some value,_))) _ _)))) => some (pointer.number,value.number)
  | _ => none

theorem source_allocation_precedes_ordering : output.1.toOption.map
    (fun file => file.globs.map (fun pair => binders pair.2)) =
      some [some (13,14),some (17,18),some (15,16)] := by cbv

theorem actual_freshness : output.2.freshness.next = 19 := by cbv

theorem all_generated_dependencies_empty : output.1.toOption.map
    (fun file => file.globs.map (fun pair => GlobalOrder.freeGlobal pair.2)) =
      some [.ok [],.ok [],.ok []] := by cbv

theorem runtime_name_is_not_dependency :
    GlobalOrder.freePure (call (.sym conversion) [Construction.integer 0]) = .ok [] := by cbv

theorem runtime_argument_is_dependency :
    GlobalOrder.freePure (call (.sym conversion) [symbolPure gX]) = .ok [gX] := by cbv

theorem first_operand_is_outside_binder_scope :
    GlobalOrder.freeEffect (strongSequence (symbolPattern gX (.loaded .integer))
      (pureEffect (symbolPure gX)) (pureEffect (symbolPure gX))) = .ok [gX] := by cbv

theorem nonempty_dependency_reject :
    GlobalOrder.mergeIndependent [(gX,.definition (.loaded .integer,intType)
      (pureEffect (symbolPure gY)))] =
      .error "unsupported: nonempty global dependencies need actual topological ordering" := by cbv

theorem semantic_duplicate_reject :
    GlobalOrder.mergeIndependent [(gX,.declaration (.object .pointer,intType)),
      ({gX with description := .id "other_name"},.declaration (.object .pointer,intType))] =
        .error "unsupported: duplicate global semantic keys" := by cbv

#print axioms GlobalOrder.freePure
#print axioms GlobalOrder.freeEffect
#print axioms GlobalOrder.mergeIndependent
#print axioms actual_three_global_order
#print axioms source_allocation_precedes_ordering
#print axioms actual_freshness
#print axioms all_generated_dependencies_empty
#print axioms runtime_name_is_not_dependency
#print axioms runtime_argument_is_dependency
#print axioms first_operand_is_outside_binder_scope
#print axioms nonempty_dependency_reject
#print axioms semantic_duplicate_reject
end SourceGlobalIndependentTests
