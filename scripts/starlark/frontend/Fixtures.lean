module

import Lean.Data.Json
import Silmaril.Languages.Starlark.Frontend.Checks
meta import Silmaril.Languages.Starlark.Frontend.Checks
import Silmaril.Languages.Starlark.Frontend.Module.Checks
meta import Silmaril.Languages.Starlark.Frontend.Module.Checks
import Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.SpreadChecks
import Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ComputedCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ReturnCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.AssignmentCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.AssignmentCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.CallStatementChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.CallStatementChecks
import Silmaril.Languages.Starlark.Frontend.Module.LogicalCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.LogicalCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.ConditionalCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ConditionalCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.BranchCallChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.BranchCallChecks
import Silmaril.Languages.Starlark.Frontend.Module.ListDisplayChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.ListDisplayChecks
import Silmaril.Languages.Starlark.Frontend.Module.TupleDisplayChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.TupleDisplayChecks
import Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks
meta import Silmaril.Languages.Starlark.Frontend.Module.Loader.Checks
import Silmaril.Languages.Starlark.Frontend.Module.Loader.KeywordOnlyChecks
meta import Silmaril.Languages.Starlark.Frontend.Module.Loader.KeywordOnlyChecks

open Lean Silmaril.Languages.Starlark.Frontend
open Silmaril.Languages.Starlark.Frontend.Module
  (Observation controls spreadControls computedCallControls returnCallControls assignmentCallControls callStatementControls logicalCallControls
    conditionalCallControls branchCallControls branchSyntaxControls branchSpanSource branchTestSpans
    listDisplayControls listSyntaxControls listSpanSource listDisplaySpans
    tupleDisplayControls tupleSyntaxControls tupleSpanSource tupleDisplaySpans)

private def moduleObservation (expected : Observation) : Json :=
  let (phase, want) := match expected with
    | .exportedInt value => ("publication", toString value)
    | .undefinedName name => ("validation", s!"undefined: {name}")
    | .missingArgument name => ("runtime", s!"missing 1 argument ({name})")
    | .multipleValues name => ("runtime", s!"multiple values for parameter {reprStr name}")
    | .duplicateKey name => ("runtime", s!"duplicate key: {reprStr name}")
    | .duplicateExplicitKeyword name => ("validation", s!"keyword argument {reprStr name} is repeated")
    | .requiredAfterDefault _ => ("validation", "required parameter may not follow optional")
    | .invalidStar => ("runtime", "argument after * must be iterable")
    | .invalidStarStar => ("runtime", "argument after ** must be a mapping")
    | .uninitializedGlobal name => ("runtime", s!"global variable {name} referenced before assignment")
    | .uninitializedLocal name => ("runtime", s!"local variable {name} referenced before assignment")
  Json.mkObj [("phase", toJson phase), ("want", toJson want)]

private def spanCoordinates (spans : List Span) : Json :=
  toJson (spans.map fun span => [span.start.line, span.start.column, span.stop.line, span.stop.column])

private def loaderObservation (phase want marker wrapper : String) (sources : List (String × String))
    (requests : List String) : Json :=
  Json.mkObj [("phase", toJson phase), ("want", toJson want), ("marker", toJson marker),
    ("wrapper", toJson wrapper), ("sources", Json.mkObj (sources.map fun (label, source) =>
      (label, toJson source))), ("requests", toJson requests)]

private def loaderFixture (control : Silmaril.Languages.Starlark.Frontend.Module.Loader.Control) : Json :=
  let label := Silmaril.Languages.Starlark.Frontend.Module.Loader.label
  let producer := Silmaril.Languages.Starlark.Frontend.Module.Loader.producer
  let (phase, want, marker) := match control.expected with
    | .exportedInt value | .wrapperExportedInt value => ("publication", toString value, "")
    | .missingExport name => ("runtime", s!"name {name} not found in module {label}", "")
    | .wrapperArgumentError name => ("runtime", s!"missing 1 argument ({name})", "")
    | .lateLoad => ("runtime", s!"name absent not found in module {label}", "99")
    | .privateImport name => ("validation", s!"names with leading underscores are not exported: {name}", "")
    | .emptyLoad => ("parse", "load statement must import at least 1 symbol", "")
    | .loadInFunction => ("validation", "load statement within a function", "")
  let wrapper := match control.expected with
    | .wrapperExportedInt _ => "relay"
    | _ => ""
  let loader := loaderObservation phase want marker wrapper [(label, producer)] [label]
  Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
    ("accepts", toJson (phase != "parse")), ("loader", loader)]

open Silmaril.Languages.Starlark.Frontend.Module.Loader
  (KeywordControl HeaderControl keywordProducerLabel keywordWrapperLabel keywordProducer keywordWrapper
    keywordOnlyControls headerControls headerSpanSource headerFormalSpans requiredOnlySource)

private def keywordLoaderFixture (control : KeywordControl) : Json :=
  let (phase, want) := match control.expected with
    | .exported value => ("publication", toString value)
    | .missing name => ("runtime", s!"missing 1 argument ({name})")
    | .positionalOverflow capacity count => ("runtime", s!"{capacity} positional argument ({count} given)")
  let loader := loaderObservation phase want "" ""
    [(keywordProducerLabel, keywordProducer), (keywordWrapperLabel, keywordWrapper)]
    [keywordWrapperLabel, keywordProducerLabel]
  Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
    ("accepts", toJson true), ("loader", loader)]

private def headerFixture (control : HeaderControl) : Json :=
  let fields := [("name", toJson control.name), ("source", toJson control.source),
    ("accepts", toJson control.goAccepts)]
  match control.goValidationError with
  | none => Json.mkObj fields
  | some message => Json.mkObj (fields ++ [("module",
      Json.mkObj [("phase", toJson "validation"), ("want", toJson message)])])

public def main (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "expected one fixture output path")
  let entries := fixtures.toArray.map fun fixture => Json.mkObj
    [("name", toJson fixture.name), ("source", toJson fixture.source),
     ("accepts", toJson fixture.goAccepts)]
  let moduleControls := controls ++ spreadControls ++ computedCallControls ++
    returnCallControls ++ assignmentCallControls ++ callStatementControls ++ logicalCallControls ++
      conditionalCallControls ++ branchCallControls ++ listDisplayControls ++ tupleDisplayControls
  let modules := moduleControls.toArray.map fun control =>
    Json.mkObj [("name", toJson control.name), ("source", toJson control.source),
      ("accepts", toJson true), ("module", moduleObservation control.expected)]
  let loaders := Silmaril.Languages.Starlark.Frontend.Module.Loader.controls.toArray.map loaderFixture ++
    keywordOnlyControls.toArray.map keywordLoaderFixture
  let moduleSyntax := (branchSyntaxControls ++ listSyntaxControls ++ tupleSyntaxControls).toArray.map
    fun (name, source, _, accepts) =>
      Json.mkObj [("name", toJson name), ("source", toJson source), ("accepts", toJson accepts)]
  let branchSpans := Json.mkObj [("name", toJson "utf8-branch-test-spans"),
    ("source", toJson branchSpanSource), ("accepts", toJson true),
    ("branchTests", spanCoordinates branchTestSpans)]
  let listSpans := Json.mkObj [("name", toJson "utf8-list-display-spans"),
    ("source", toJson listSpanSource), ("accepts", toJson true),
    ("listDisplays", spanCoordinates listDisplaySpans)]
  let tupleSpans := Json.mkObj [("name", toJson "utf8-tuple-display-spans"),
    ("source", toJson tupleSpanSource), ("accepts", toJson true),
    ("tupleDisplays", spanCoordinates tupleDisplaySpans)]
  let headerSpans := Json.mkObj [("name", toJson "utf8-keyword-only-formal-spans"),
    ("source", toJson headerSpanSource), ("accepts", toJson true),
    ("headerFormals", spanCoordinates headerFormalSpans)]
  let requiredOnly := Json.mkObj [("name", toJson "go-required-only-bare-star"),
    ("source", toJson requiredOnlySource), ("accepts", toJson true),
    ("module", moduleObservation (.exportedInt 7))]
  IO.FS.writeFile output
    (Json.arr (entries ++ modules ++ loaders ++ moduleSyntax ++ headerControls.toArray.map headerFixture ++
      #[branchSpans, listSpans, tupleSpans, headerSpans, requiredOnly])).compress
