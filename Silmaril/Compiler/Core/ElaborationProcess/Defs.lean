module

public import Silmaril.Cerberus.Elaboration.Functions.Defs
public import Silmaril.Compiler.Core.ElaborationCorrectness.Defs
public import Silmaril.Compiler.Category.Cerberus.Process.Defs

/-! A restricted actual typed-Ail program and the Core file assembled by its
elaboration. This workflow connects the real function elaborator to the existing
Core process institution. The source is a single zero-argument signed-int main
with a block containing a literal return. It does not define an independent Ail
semantics or a native compiler certificate.
-/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationProcess
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Elaboration
open Construction

/-- Parameters of one actual typed-Ail function, retaining source annotations. -/
structure LiteralMain where
  symbol : Sym
  location : Loc
  marker : Nat
  attributes : Attributes
  blockDesugaring : Ail.DesugInfo
  statementLocation : Loc
  expressionLocation : Loc
  returnDesugaring : Ail.DesugInfo
  statementAttributes : Attributes
  returnAnnotations : List Annot
  number : Int
  basis : Ail.Basis
  suffix : Option Ail.IntegerSuffix

def LiteralMain.returnType (source : LiteralMain) : Ctype :=
  .mk source.returnAnnotations (.basic (.integer (.signed .int)))

def LiteralMain.body (source : LiteralMain) : Ail.TypedStatement :=
  .mk source.location source.blockDesugaring (.mk []) (.block []
    [ElaborationCorrectness.returnLiteral source.statementLocation source.expressionLocation
      source.returnDesugaring source.statementAttributes source.number source.basis source.suffix])

/-- Existing Ail syntax, without a substitute source language or supplied Core body. -/
def LiteralMain.program (source : LiteralMain) : Ail.TypedProgram :=
  (some source.symbol, {
    declarations := [(source.symbol, source.location, source.attributes,
      .function true (⟨false, false, false⟩, source.returnType) [] false false false)]
    objectDefinitions := []
    functionDefinitions := [(source.symbol, {
      loc := source.location, marker := source.marker, attrs := source.attributes
      params := [], body := source.body })]
    staticAssertions := [], tagDefinitions := [],
    externIdmap := [(⟨source.location, "main"⟩, source.symbol, .definition)], typedefAttributes := []
    loopAttributes := [], cnFunctions := [], cnLemmata := [], cnPredicates := []
    cnDatatypes := [], cnDeclSpecs := [], cnIdents := [] })

def returnLabel (freshness : Freshness.Context) : Sym :=
  ⟨freshness.digest, freshness.next, .id s!"ret_{freshness.next}"⟩

def returnTemporary (freshness : Freshness.Context) : Sym :=
  ⟨freshness.digest, freshness.next + 1, .none⟩

def saveTemporary (freshness : Freshness.Context) : Sym :=
  ⟨freshness.digest, freshness.next + 2, .none⟩

/-- The body description whose construction is proved by `literal_elaborate`. -/
def LiteralMain.coreBody (source : LiteralMain) (freshness : Freshness.Context)
    (conversion : Sym) : Effect :=
  addLocation source.location (addStatement
    (Statements.unitSequence [ElaborationCorrectness.returnCore
      (returnTemporary freshness) (returnLabel freshness) conversion
      source.statementLocation source.expressionLocation source.statementAttributes
      source.returnAnnotations source.number] skip))

/-- Actual function/file assembly, including the saved return label and metadata. -/
def LiteralMain.bindings (source : LiteralMain) (runtime : Functions.RuntimeInputs)
    (freshness : Freshness.Context) (conversion : Sym) : Codec.FileBindings where
  main := some source.symbol
  callingConvention := .normal
  tagDefs := []
  stdlib := runtime.stdlib
  impl := runtime.impl
  globs := []
  funs := [(source.symbol, .procedure source.location (some source.marker) (.loaded .integer) []
    (strongSequence (wildcard .unit) (source.coreBody freshness conversion)
      (Functions.returnSave (some source.symbol) source.symbol (returnLabel freshness)
        (saveTemporary freshness) source.location source.returnType (.loaded .integer))))]
  extern := [(⟨source.location, "main"⟩, [source.symbol], .normal source.symbol)]
  funInfo := [(source.symbol, source.location, source.attributes, source.returnType, [], false, true)]
  loopAttributes := []
  visibleObjects := []

/-- Package the returned wire bindings as their actual Core semantic file.
Provenance strings and enum registry are transport inputs, not proof evidence. -/
def document (bindings : Codec.FileBindings) (commit implementation : String)
    (enums : Option (List (Sym × IntegerType))) : Codec.Document :=
  ⟨commit, implementation, bindings, bindings.toFile, rfl, enums⟩

def finalContext (freshness : Freshness.Context) : State.Context :=
  State.initial {freshness with next := freshness.next + 3} .normal "Driver"

end Silmaril.Compiler.Core.ElaborationProcess
