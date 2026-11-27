module

import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Thms
meta import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Defs

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Parquet Silmaril.Formats.Arrow
open Int32ByteArrayGroup.File (Kind Value)
open Silmaril.Formats.Relational.NamedTable (Packed)

private def schema (order : Order) : Schema := ⟨"n", "blob", ⟨"day", "label", order⟩⟩
private def dateFirst := schema .dateFirst
private def textFirst := schema .textFirst
private def limits : Limits :=
  ⟨⟨2, 3, 5⟩, ⟨⟨8192, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 20⟩⟩, {}⟩, 3, 5⟩⟩
private def custom : PartitionPath.Options := {nullMarker := "null/=%"}

private def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

private structure Sample where
  int : Option Int32
  blob : Option Bytes
  day : Option Int32
  label : Option Bytes

private def leap := some (utf8 "café/blue")
private def input : List Sample :=
  [⟨some (-7), some (.ofList [255, 0]), some 19782, leap⟩,
    ⟨some 0, some (utf8 "x"), none, some (utf8 "")⟩,
    ⟨none, some .empty, some 19782, leap⟩,
    ⟨some 9, some (utf8 "y"), some (-719528), none⟩,
    ⟨none, none, none, some (utf8 "")⟩,
    ⟨some 11, none, some 19782, leap⟩]

private def dbOf (layout : Schema) (samples : List Sample) : Packed String String Value := fun name =>
  if name == "source" then
    some ⟨layout.toScan, samples.flatMap fun sample =>
      (Int32ByteArrayGroup.File.rows layout.intField layout.byteField [(sample.int, sample.blob)]).map
        fun row => TypedPartitions.extendRow row (layout.keys.cells sample.day sample.label)⟩
  else none

private def make (layout : Schema) (options : PartitionPath.Options) :=
  emit (dbOf layout input) "source" layout options limits

private def showCell : (kind : Kind) → Option (Value kind) → String
  | .int32 _, some value => toString value.toInt
  | .byteArray _, some bytes => "b:" ++ String.intercalate "," (bytes.toList.map (fun byte => toString byte.toNat))
  | _, none => "null"

private def observed (layout : Schema) (row : Scan.Row layout.toScan Value) : List String :=
  List.ofFn fun i => showCell (layout.toScan.kind i).2 (row i)

private def defaultPaths :=
  ["day=2024-02-29/label=caf%C3%A9%2Fblue/part-0.parquet",
    "day=__HIVE_DEFAULT_PARTITION__/label=/part-0.parquet",
    "day=0000-01-01/label=__HIVE_DEFAULT_PARTITION__/part-0.parquet"]

private def customPaths :=
  ["label=caf%C3%A9%2Fblue/day=2024-02-29/part-0.parquet", "label=/day=null%2F%3D%25/part-0.parquet",
    "label=null%2F%3D%25/day=0000-01-01/part-0.parquet"]

#guard Id.run do
  let .ok files := make dateFirst {} | return false
  let .ok trace := readManifest dateFirst {} limits files | return false
  let .eos := trace.termination | return false
  return files.map (·.path) == defaultPaths && files.map (·.groupRows) == [[2, 1], [2], [1]] &&
    trace.batches.map (·.rowCount) == [2, 1, 2, 1] &&
    trace.rows.map (observed dateFirst) ==
      [["-7", "b:255,0", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["null", "b:", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["11", "null", "19782", "b:99,97,102,195,169,47,98,108,117,101"],
       ["0", "b:120", "null", "b:"], ["null", "null", "null", "b:"], ["9", "b:121", "-719528", "null"]]

#guard Id.run do
  let .ok files := make textFirst custom | return false
  let .ok trace := readManifest textFirst custom limits files | return false
  let .eos := trace.termination | return false
  return files.map (·.path) == customPaths && trace.batches.map (·.rowCount) == [2, 1, 2, 1] &&
    trace.rows.head?.map (observed textFirst) ==
      some ["-7", "b:255,0", "b:99,97,102,195,169,47,98,108,117,101", "19782"]

#guard Id.run do
  let .ok [] := emit (dbOf dateFirst []) "source" dateFirst {} limits | return false
  let .ok trace := readManifest dateFirst {} limits [] | return false
  let .eos := trace.termination | return false
  return trace.batches.isEmpty

#guard match emit (dbOf dateFirst input) "missing" dateFirst {} limits,
    emit (dbOf dateFirst input) "source" textFirst {} limits with
  | .error .missingName, .error .schemaMismatch => true
  | _, _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with cuts.rowsPerGroup := 0} with
  | .error (.policy .zeroRowsPerGroup) => true
  | _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with cuts.maxGroupsPerFile := 1} with
  | .error (.cuts path .groupLimit) => path == defaultPaths[0]!
  | _ => false

#guard match emit (dbOf dateFirst input) "source" dateFirst {}
    {limits with writer.maxGroups := 1} with
  | .error (.parquet path .groupLimit) => path == defaultPaths[0]!
  | _ => false

-- The first bucket fits and the later leap bucket exceeds the native group cap.
#guard match emit (dbOf dateFirst (input.drop 1 ++ input.take 1)) "source" dateFirst {}
    {limits with writer.maxGroups := 1} with
  | .error (.parquet path .groupLimit) => path == defaultPaths[0]!
  | _ => false

-- A late routing error precedes the writer cap, even with an admitted prefix.
#guard
  let collision : Sample := ⟨none, none, none, some (utf8 "__HIVE_DEFAULT_PARTITION__")⟩
  match emit (dbOf dateFirst (input ++ [collision])) "source" dateFirst {} {limits with writer.maxGroups := 0} with
  | .error (.routing (.row 6 (.render (.nullMarkerCollision "label")))) => true
  | _ => false

#print axioms namedRows_of_observe
#print axioms fileInput_rows
#print axioms FileMatches.cutBounds
#print axioms emit_routing_error
#print axioms emit_readback

private def writeFixture (root : System.FilePath) (layout : Schema)
    (options : PartitionPath.Options) : IO Unit := do
  let .ok files := make layout options | throw (IO.userError "paired Hive emission failed")
  let .ok trace := readManifest layout options limits files | throw (IO.userError "paired Hive ingress failed")
  let .eos := trace.termination | throw (IO.userError "paired Hive read did not reach EOS")
  for file in files do
    let path := root / file.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile path file.bytes.data
  IO.FS.writeFile (root / "inventory.txt") (String.intercalate "\n" (files.map (·.path)) ++ "\n")
  let batches := trace.batches.flatMap fun batch =>
    toString batch.rowCount :: batch.toRows.map (fun row => String.intercalate "\t" (observed layout row))
  IO.FS.writeFile (root / "batches.tsv") (String.intercalate "\n" batches ++ "\n")

public def runWriterChecks (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "usage: Checks.lean <fixture-root>")
  writeFixture (System.FilePath.mk root / "date-first") dateFirst {}
  writeFixture (System.FilePath.mk root / "text-first") textFirst custom

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.runWriterChecks
