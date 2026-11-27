module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Date32.Utf8.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Date32.Utf8.Defs

namespace Silmaril.Formats.Hive.Date32.Utf8

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def dateFirst : Keys := ⟨"day", "label", .dateFirst⟩
private def textFirst : Keys := ⟨"day", "label", .textFirst⟩
private def clean : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def first := "label=caf%C3%A9%2fblue/%64ay=2024%2d02%2D29/A%2Eparquet"
private def emptyLabel := "day=__HIVE_DEFAULT_PARTITION__/label=/B.parquet"
private def nullLabel := "day=0000-01-01/label=%5F%5FHIVE_DEFAULT_PARTITION__/C.parquet"

private def paths := [first, emptyLabel, nullLabel, first]

private def lookup (path : String) : Except String Bytes :=
  if paths.contains path then .ok clean else .error "missing literal snapshot"

private def project (keys : Keys) (positions : Array (Fin 4)) :
    Scan.Projection (keys.schema.extend physical) := by
  rcases keys with ⟨dateName, textName, order⟩
  cases order <;> exact Scan.Projection.ofArray positions

private def full (keys : Keys) := project keys #[0, 1, 2, 3]

private def repeated (keys : Keys) := project keys #[3, 0, 2, 3]

private def run (keys : Keys) (projection : Scan.Projection (keys.schema.extend physical))
    (declared : List String) :=
  scanPaths (keys := keys) (int32 := ordinal) (byteArray := payload) {} {} lookup projection
    (fun _ => some true) declared

private def showCell : (kind : Kind) → Option (Value kind) → String
  | .int32 _, some value => toString value.toInt
  | .byteArray _, some bytes => "b:" ++ String.intercalate "," (bytes.toList.map (fun byte => toString byte.toNat))
  | _, none => "null"

private def labels (schema : Scan.Schema String Kind) : List String :=
  List.ofFn fun column => (schema.kind column).1

private def observe {schema : Scan.Schema String Kind} (row : Scan.Row schema Value) : List String :=
  List.ofFn fun column => showCell (schema.kind column).2 (row column)

#guard Id.run do
  let .ok date := preparePaths ordinal payload dateFirst {} paths | return false
  let .ok text := preparePaths ordinal payload textFirst {} paths | return false
  return date.map (·.path.declared) == paths && text.map (·.path.declared) == paths &&
    date.map (fun file => observe file.cells) ==
      [["19782", "b:99,97,102,195,169,47,98,108,117,101"], ["null", "b:"], ["-719528", "null"],
        ["19782", "b:99,97,102,195,169,47,98,108,117,101"]] &&
    text.map (fun file => observe file.cells) == date.map (fun file => (observe file.cells).reverse)

#guard Id.run do
  let .ok runDate := run dateFirst (full dateFirst) paths | return false
  let .ok runText := run textFirst (full textFirst) paths | return false
  let .eos := runDate.termination | return false
  let .eos := runText.termination | return false
  return labels (full dateFirst).schema == ["ordinal", "payload", "day", "label"] &&
    labels (full textFirst).schema == ["ordinal", "payload", "label", "day"] &&
    runDate.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2, 3, 0, 2, 3, 0, 2] &&
    runText.batches.map (·.rowCount) == runDate.batches.map (·.rowCount) &&
    runDate.rows.head?.map observe ==
      some ["-2147483648", "null", "19782", "b:99,97,102,195,169,47,98,108,117,101"] &&
    runText.rows.map observe == runDate.rows.map (fun row => (observe row).take 2 ++ ((observe row).drop 2).reverse)

#guard Id.run do
  let .ok all := run dateFirst (full dateFirst) paths | return false
  let .ok subset := run dateFirst (repeated dateFirst) paths | return false
  let .ok zero := run dateFirst (Scan.Projection.ofArray #[]) paths | return false
  return labels (repeated dateFirst).schema == ["label", "ordinal", "day", "label"] &&
    subset.rows.map observe == all.rows.map (fun row =>
      let values := observe row
      [values[3]!, values[0]!, values[2]!, values[3]!]) &&
    zero.batches.map (·.rowCount) == all.batches.map (·.rowCount) && zero.rows.length == all.rows.length

private def doubleFailure := "day=2024%2D02%2d30/invalid.parquet"
private def noSnapshot := "day=2024-02-29/label=ok/missing.parquet"

-- A binding failure is reached before any lookup, including an earlier missing snapshot.
#guard match run dateFirst (full dateFirst) [noSnapshot, doubleFailure, "../unreached.parquet"] with
  | .error (.binding path (.conversion "day" (.invalidDate "2024-02-30"))) => path == doubleFailure
  | _ => false

#guard match run textFirst (full textFirst) [first, doubleFailure] with
  | .error (.binding path (.missingKey "label")) => path == doubleFailure
  | _ => false

#guard
  let invalid := "day=2024-02-30/label=%FF/invalid.parquet"
  match run dateFirst (full dateFirst) [first, invalid] with
  | .error (.partitionPath path .invalidUtf8) => path == invalid
  | _ => false

#guard
  let invalid := "day=2024-02-29/%64ay=2024-02-29/label=x/invalid.parquet"
  match run dateFirst (full dateFirst) [invalid] with
  | .error (.partitionPath path (.duplicateKey "day")) => path == invalid
  | _ => false

#guard
  let keys : Keys := ⟨"day", "ordinal", .textFirst⟩
  match run keys (full keys) [] with
  | .error (.schema (.physicalCollision "ordinal")) => true
  | _ => false

#guard match run dateFirst (full dateFirst) [first, noSnapshot, first] with
  | .ok trace =>
    trace.batches.map (·.rowCount) == [3, 0, 2] &&
      decide (trace.termination = .readError (.open noSnapshot (.lookup "missing literal snapshot")))
  | _ => false

#print axioms Keys.schema_order
#print axioms decode_eq_fields
#print axioms convert_date
#print axioms convert_text
#print axioms preparePaths_paths
#print axioms preparePaths_first_binding_error
#print axioms scanPaths_admission_error
#print axioms scanPaths_eq_reference

private def writeTrace (directory : System.FilePath) (name : String) (keys : Keys)
    (projection : Scan.Projection (keys.schema.extend physical)) : IO Unit := do
  let .ok trace := run keys projection paths | throw (IO.userError "DATE/UTF-8 path admission failed")
  let .eos := trace.termination | throw (IO.userError "DATE/UTF-8 scan did not reach EOS")
  let batches := trace.batches.flatMap fun batch =>
    toString batch.rowCount :: batch.toRows.map (fun row => String.intercalate "\t" (observe row))
  let header := String.intercalate "\t" (labels projection.schema)
  IO.FS.writeFile (directory / (name ++ ".tsv")) (String.intercalate "\n" (header :: batches) ++ "\n")

public def runChecks (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "usage: Checks.lean <oracle-fixture-directory>")
  let directory : System.FilePath := root
  for path in paths do
    let file := directory / path
    if let some parent := file.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile file clean.data
  IO.FS.writeFile (directory / "inventory.txt") (String.intercalate "\n" paths ++ "\n")
  writeTrace directory "date-first" dateFirst (full dateFirst)
  writeTrace directory "text-first" textFirst (full textFirst)
  writeTrace directory "repeated" dateFirst (repeated dateFirst)

end Silmaril.Formats.Hive.Date32.Utf8

public def main : List String → IO Unit := Silmaril.Formats.Hive.Date32.Utf8.runChecks
