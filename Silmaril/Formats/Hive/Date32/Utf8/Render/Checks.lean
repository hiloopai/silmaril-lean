module

import Silmaril.Formats.Hive.Date32.Utf8.Render.Thms
import Silmaril.Formats.Hive.WritePlan.Restore.Thms
meta import Silmaril.Formats.Hive.Date32.Utf8.Render.Defs

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File (Kind Value)

private def dateFirst : Keys := ⟨"day", "label", .dateFirst⟩
private def textFirst : Keys := ⟨"day", "label", .textFirst⟩
private def escapedKeys : Keys := ⟨"d/é=%", "l=/%", .textFirst⟩
private def customMarker : PartitionPath.Options := {nullMarker := "null/=%"}
private def dateMarker : PartitionPath.Options := {nullMarker := "2000-02-29"}

private def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

private structure Fixture where
  name : String
  keys : Keys
  options : PartitionPath.Options
  day : Option Int32
  text : Option Bytes
  directory : String

private def fixtures : List Fixture :=
  [⟨"date-first", dateFirst, {}, some 19782, some (utf8 "café/=blue%"),
      "day=2024-02-29/label=caf%C3%A9%2F%3Dblue%25"⟩,
    ⟨"text-first", textFirst, {}, some 19782, some (utf8 "café/=blue%"),
      "label=caf%C3%A9%2F%3Dblue%25/day=2024-02-29"⟩,
    ⟨"empty", dateFirst, {}, none, some (utf8 ""), "day=__HIVE_DEFAULT_PARTITION__/label="⟩,
    ⟨"null", textFirst, {}, some (-719528), none, "label=__HIVE_DEFAULT_PARTITION__/day=0000-01-01"⟩,
    ⟨"escaped-marker-and-keys", escapedKeys, customMarker, none, none,
      "l%3D%2F%25=null%2F%3D%25/d%2F%C3%A9%3D%25=null%2F%3D%25"⟩,
    ⟨"date-marker", dateFirst, dateMarker, none, some (utf8 "plain"), "day=2000-02-29/label=plain"⟩,
    ⟨"plain-date-first", dateFirst, {}, some (-1), some (utf8 "plain"), "day=1969-12-31/label=plain"⟩,
    ⟨"plain-text-first", textFirst, {}, some (-1), some (utf8 "plain"), "label=plain/day=1969-12-31"⟩]

private def sameCell : (kind : Kind) → Option (Value kind) → Option (Value kind) → Bool
  | .int32 _, left, right => left == right
  | .byteArray _, left, right => left == right

private def prepared (fixture : Fixture) (directory : String) : Bool := Id.run do
  let keys := fixture.keys
  let original := keys.cells fixture.day fixture.text
  let path := directory ++ "/A%2Eparquet"
  let .ok file := Manifest.prepareFile keys.schema fixture.options convert path | return false
  return file.path.declared == path && file.path.canonicalDirectory == directory &&
    file.path.filename == "A%2Eparquet" &&
    (List.finRange keys.schema.toScan.width).all fun i =>
      sameCell (keys.schema.toScan.kind i).2 (file.cells i) (original i)

#guard fixtures.all fun sample =>
  let actual := renderDirectory (keys := sample.keys) sample.options (sample.keys.cells sample.day sample.text)
  actual.toOption == some sample.directory && prepared sample sample.directory

private def refusal (keys : Keys) (options : PartitionPath.Options) (day : Option Int32) (text : Option Bytes) :
    Option (WritePlan.RowError EncodeError) :=
  match renderDirectory (keys := keys) options (keys.cells day text) with
  | .error reason => some reason
  | .ok _ => none

#guard refusal dateFirst {} none (some (utf8 "__HIVE_DEFAULT_PARTITION__")) ==
  some (.render (.nullMarkerCollision "label"))

#guard refusal dateFirst dateMarker (some 11016) (some (utf8 "2000-02-29")) ==
  some (.render (.nullMarkerCollision "day")) &&
  refusal textFirst dateMarker (some 11016) (some (utf8 "2000-02-29")) ==
    some (.render (.nullMarkerCollision "label"))

#guard refusal escapedKeys customMarker none (some (utf8 "null/=%")) ==
  some (.render (.nullMarkerCollision escapedKeys.text))

-- A literal percent spelling is escaped again and remains present.
#guard (renderDirectory (keys := dateFirst) dateMarker
    (dateFirst.cells none (some (utf8 "2000%2D02%2D29")))).toOption ==
  some "day=2000-02-29/label=2000%252D02%252D29"

#guard refusal dateFirst {} none (some ⟨⟨#[0xFF]⟩⟩) == some (.encode "label" .invalidUtf8)

#guard refusal dateFirst {} (some 2932897) none == some (.encode "day" (.date (.outsideDateProfile 2932897)))

#guard refusal dateFirst {nullMarker := ""} none none == some (.render .emptyNullMarker) &&
  refusal dateFirst {requiredKeys := ["third"]} none none == some (.render (.missingKey "third")) &&
  refusal ⟨"day", "day", .dateFirst⟩ {} none none == some (.render (.duplicateKey "day"))

#print axioms WritePlan.encodeEntries_keys
#print axioms WritePlan.decode_renderedEntries
#print axioms encode_convert_leftInverse
#print axioms renderDirectory_parse
#print axioms prepareFile_renderDirectory
#print axioms renderDirectory_first_markerCollision

public def runRenderChecks (args : List String) : IO Unit := do
  let [output] := args | throw (IO.userError "usage: Checks.lean <rendered-directories.tsv>")
  let lines ← fixtures.mapM fun fixture => do
    let keys := fixture.keys
    let .ok directory := renderDirectory (keys := keys) fixture.options (keys.cells fixture.day fixture.text) |
      throw (IO.userError s!"render failed for {fixture.name}")
    unless prepared fixture directory do
      throw (IO.userError s!"checked readback failed for {fixture.name}")
    return fixture.name ++ "\t" ++ directory
  IO.FS.writeFile output (String.intercalate "\n" lines ++ "\n")

end Silmaril.Formats.Hive.Date32.Utf8

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.Utf8.runRenderChecks
