import Silmaril.Cerberus.Elaboration.Functions.Defs
import Silmaril.Cerberus.Ail.Codec.Defs

/-! Compare the actual narrow elaborator with genuine pinned Cerberus exports.

Usage: `lake env lean --run tests/cerberus/ElaborationOracle.lean DIRECTORY`
where each fixture has `tail.sexp.gz`, `core.sexp.gz` and `fresh-context.json`.
Uncompressed `.sexp` files are accepted for isolated exporter workflows.

The elaborator receives only actual typed Ail, the pinned target, enum bindings,
the measured pre-translation freshness context, and the exported runtime maps
and independently captured runtime parser name map.
Expected Core functions, bodies and metadata are used only for comparison.
This is exact differential evidence for the selected fixtures, not a theorem of
general elaboration equivalence or an implementation of the remaining syntax.
-/

open Silmaril.Cerberus
open Silmaril.Cerberus
open Silmaril.Cerberus.Elaboration
open Silmaril.TaggedCodec
open Silmaril.Formats.SExpEncoding

private def checked {α : Type} (context : String) : Except String α → IO α
  | .ok value => pure value
  | .error why => throw <| IO.userError s!"{context}: {why}"

private def readWire (directory : System.FilePath) (stem : String) : IO String := do
  let plain := directory / s!"{stem}.sexp"
  if ← plain.pathExists then IO.FS.readFile plain
  else
    let compressed := directory / s!"{stem}.sexp.gz"
    let result ← IO.Process.output {cmd := "gzip", args := #["-dc", compressed.toString]}
    unless result.exitCode == 0 do
      throw <| IO.userError s!"{compressed}: decompression failed: {result.stderr}"
    pure result.stdout

/-- Runtime `ailnames` is captured directly after `load_core_stdlib`, before
frontend processing or translation. No expected function metadata is inspected. -/
private def readAliases (directory : System.FilePath) : IO (List (String × Sym)) := do
  let path := directory / "shared" / "runtime" / "ailnames.sexp"
  let text ← IO.FS.readFile path
  let some tree := parseTagged? text
    | throw <| IO.userError s!"{path}: invalid tagged runtime alias map"
  unless printTagged tree ++ "\n" == text do
    throw <| IO.userError s!"{path}: noncanonical runtime alias map"
  let codec := Silmaril.TaggedCodec.Codec.map Silmaril.TaggedCodec.Codec.str Codec.sym
  match codec.decode tree with
  | .ok aliases => pure aliases
  | .error why => throw <| IO.userError s!"{path}: runtime alias decoding: {repr why}"

private def snapshot (name : String) (snapshots : Array Lean.Json) : Except String Lean.Json := do
  let selected ← snapshots.toList.filterM fun value => do
    return (← value.getObjValAs? String "phase") == name
  match selected with
  | [value] => pure value
  | _ => throw s!"expected exactly one {name} snapshot"

private def readFreshness (directory : System.FilePath) :
    IO (Freshness.Context × Nat) := do
  let text ← IO.FS.readFile (directory / "fresh-context.json")
  let state ← checked s!"{directory}: freshness JSON" <| Lean.Json.parse text
  let snapshots ← checked s!"{directory}: freshness snapshots" <|
    state.getObjValAs? (Array Lean.Json) "snapshots"
  checked s!"{directory}: measured freshness" do
    let before ← snapshot "before_Translation_translate" snapshots
    let next ← before.getObjValAs? Nat "next"
    let last ← before.getObjValAs? Int "lastAllocated"
    unless last + 1 == (next : Int) do throw "counter/next snapshot inconsistency"
    let maximum ← before.getObjValAs? Nat "maximum"
    unless next ≤ maximum do throw "freshness snapshot already exhausted"
    let digestHex ← before.getObjValAs? String "digestHex"
    let some bytes := Cabs.Codec.unhex digestHex | throw "invalid fresh digest hex"
    unless bytes.size == 16 do throw "expected the actual 16-byte input digest"
    for phase in ["after_c_frontend", "after_tail_serialization"] do
      let value ← snapshot phase snapshots
      unless (← value.getObjValAs? Nat "next") == next &&
          (← value.getObjValAs? String "digestHex") == digestHex do
        throw s!"freshness changed across typed-Ail capture at {phase}"
    let after ← snapshot "after_Translation_translate" snapshots
    let expectedNext ← after.getObjValAs? Nat "next"
    unless (← after.getObjValAs? String "digestHex") == digestHex do
      throw "upstream translation changed the input digest"
    return (⟨⟨bytes.toList⟩, next, maximum⟩, expectedNext)

private structure Fixture where
  typed : Ail.TypedProgram
  core : Codec.Document
  freshness : Freshness.Context
  expectedNext : Nat

private def readFixture (directory : System.FilePath) : IO Fixture := do
  let tailText ← readWire directory "tail"
  let tail ← checked s!"{directory}: typed-Ail decoding" <|
    Ail.Codec.readTailDocument tailText
  unless Ail.Codec.printTailDocument tail == tailText do
    throw <| IO.userError s!"{directory}: noncanonical typed-Ail wire bytes"
  let .document commit implementation typed := tail
    | throw <| IO.userError s!"{directory}: genuine typed-Ail fixture rejected"
  let coreText ← readWire directory "core"
  let core ← match Codec.WellFormed.parseDocument coreText with
    | .ok value => pure value
    | .error why => throw <| IO.userError s!"{directory}: Core decoding: {repr why}"
  unless commit == core.commit && implementation == core.implementation do
    throw <| IO.userError s!"{directory}: typed-Ail/Core source or target metadata disagree"
  let (freshness, expectedNext) ← readFreshness directory
  return ⟨typed, core, freshness, expectedNext⟩

private structure Difference where
  path : String
  expected : String
  actual : String

private def fileFields : Array String :=
  #["main", "calling_convention", "tagDefs", "stdlib", "impl", "globs", "funs",
    "extern", "funinfo", "loop_attributes", "visible_objects_env"]

private def childPath (path tag : String) (index : Nat) : String :=
  if path == "generic_file" then s!"{path}.{fileFields[index]?.getD (toString index)}"
  else s!"{path}/{tag}[{index}]"

private def preview (tree : Tree) : String := s!"{(printTagged tree).take 400}"

/-- Report the first differing tagged field, retaining symbol descriptions,
annotations, locations and list/map order rather than semantic map equality. -/
private partial def firstDifference (path : String) (expected actual : Tree) :
    Option Difference :=
  match expected, actual with
  | .atom expected, .atom actual =>
      if expected == actual then none
      else some ⟨path, reprStr expected, reprStr actual⟩
  | .tag expectedTag expectedSize expectedChildren, .tag actualTag actualSize actualChildren =>
      if expectedTag != actualTag then
        some ⟨s!"{path}.tag", expectedTag, actualTag⟩
      else if expectedSize != actualSize then
        some ⟨s!"{path}.children", toString expectedSize, toString actualSize⟩
      else
        ((List.ofFn expectedChildren).zip (List.ofFn actualChildren)).zipIdx.findSome?
          fun ((expected, actual), index) =>
            firstDifference (childPath path expectedTag index) expected actual
  | _, _ => some ⟨path, preview expected, preview actual⟩

private def compareBindings (name : String) (expected actual : Codec.FileBindings) : IO Unit := do
  let expectedTree := Codec.encodeFileBindings expected
  let actualTree := Codec.encodeFileBindings actual
  let expectedBytes := (printTagged expectedTree ++ "\n").toUTF8
  let actualBytes := (printTagged actualTree ++ "\n").toUTF8
  unless expectedBytes == actualBytes do
    let difference := (firstDifference "generic_file" expectedTree actualTree).getD
      ⟨"canonical wire bytes", s!"{expectedBytes.size} bytes", s!"{actualBytes.size} bytes"⟩
    throw <| IO.userError s!"{name}: Core mismatch at {difference.path}\nexpected {difference.expected}\nactual {difference.actual}"

private def compare (directory : System.FilePath) (aliases : List (String × Sym))
    (name : String) (mustAccept : Bool) : IO Unit := do
  let fixture ← readFixture (directory / name)
  let runtime : Functions.RuntimeInputs := {
    stdlib := fixture.core.bindings.stdlib
    impl := fixture.core.bindings.impl
    aliases }
  let types : Target.Environment := ⟨Map.ofList (fixture.core.enumBindings.getD [])⟩
  let (result, after) := Functions.elaborate Target.pinnedApple types runtime fixture.typed fixture.freshness
  match result with
  | .error why =>
      if mustAccept then throw <| IO.userError s!"{name}: actual elaborator rejected: {repr why}"
      else IO.println s!"{name}: canonical inputs decoded; outside current elaborator slice ({repr why})"
  | .ok bindings =>
      compareBindings name fixture.core.bindings bindings
      unless after.freshness.next == fixture.expectedNext do
        throw <| IO.userError s!"{name}: final next fresh integer: expected {fixture.expectedNext}, actual {after.freshness.next}"
      unless after.freshness.digest == fixture.freshness.digest do
        throw <| IO.userError s!"{name}: elaborator changed the input digest"
      IO.println s!"{name}: accepted; all canonical Core file bindings and final freshness agree exactly"

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | throw <| IO.userError "expected genuine pinned elaboration oracle directory"
  let aliases ← readAliases directory
  compare directory aliases "constant-return" true
  compare directory aliases "arithmetic" true
  compare directory aliases "enum-return" true
  compare directory aliases "control-flow" true
  compare directory aliases "parameter-unused" true
  compare directory aliases "call-zeroarg" true
  compare directory aliases "global-integer" true
  compare directory aliases "global-independent" true
  compare directory aliases "global-pointer-null" true
  compare directory aliases "global-pointer-zero" true
  compare directory aliases "global-pointer-void-null" true
  compare directory aliases "cast-narrow" true
  compare directory aliases "cast-sign-extend" true
  compare directory aliases "cast-nested" true
  compare directory aliases "call-id" true
  compare directory aliases "call-two" true
  compare directory aliases "call-narrow" true
  compare directory aliases "call-nested" true
  return 0
