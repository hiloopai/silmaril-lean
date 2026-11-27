module

import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Heterogeneous.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Relational
open Hive.Manifest.Heterogeneous
open Hive.Manifest.Heterogeneous.ToIpc (convert convertProjected)
open Parquet.FlatProjection.Events (Kind Cell)
open Parquet.FlatProjection.Events.ToIpc (observation)

private def declared : Schema :=
  { fields := #[
      ⟨3, "local_us", .timestamp ⟨⟨.microsecond, none⟩, false⟩⟩,
      ⟨0, "code", .int32 false⟩, ⟨1, "label", .utf8 true⟩,
      ⟨2, "utc_ns", .timestamp ⟨⟨.nanosecond, some "UTC"⟩, true⟩⟩,
      ⟨1, "label", .utf8 true⟩]
    partitions := ⟨#[⟨"region", .utf8 true, .asNull⟩, ⟨"rank", .int32 false, .reject⟩]⟩ }

private def load (root : System.FilePath) (paths : List String) : IO (List Entry) :=
  paths.mapM fun (path : String) => do
    let bytes ← IO.FS.readBinFile (root / path)
    return ⟨path, ⟨bytes⟩⟩

private def select (positions : Array Nat) : IO (Scan.Projection declared.output) := do
  let indices ← positions.mapM fun position =>
    if valid : position < declared.output.width then pure (⟨position, valid⟩ : Fin declared.output.width)
    else throw (IO.userError s!"invalid projected position {position}")
  return Scan.Projection.ofArray indices

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def save (folder : System.FilePath) (name : String)
    {schema : Scan.Schema String Kind} (result : Except ToIpc.Error KBytes)
    (trace : Except Error (Arrow.Events.Trace schema Cell Error)) : IO Unit := do
  let wire ← require result
  let expected ← require trace
  let actual ← require (Arrow.MixedFlat.Timestamp.read {} wire)
  unless actual = observation expected do throw (IO.userError s!"{name}: Lean readback differed")
  IO.FS.writeBinFile (folder / (name ++ ".arrow")) wire.toByteArray

private def expectLate (path : String) (offset : Nat) (result : Except ToIpc.Error KBytes) : IO Unit :=
  match result with
  | .error (.source (.file 1 found (.readParquet (.column 1 3 2 (.timestamp
      (.v1 .zstd (.decode 0 start (.frame (.frame .badMagic))))))))) =>
    unless found == path && offset == start do
      throw (IO.userError "late error path or dictionary offset differed")
  | .error cause => throw (IO.userError s!"wrong late cause {repr cause}")
  | .ok _ => throw (IO.userError "late failure returned bytes")

public def main (args : List String) : IO Unit := do
  let [folder, offset] := args | throw (IO.userError "expected fixture folder and dictionary offset")
  let some offset := offset.toNat? | throw (IO.userError "invalid dictionary offset")
  let directory : System.FilePath := folder
  let nativePaths := (← IO.FS.readFile (directory / "native.txt")).splitOn "\n"
  let assembledPaths := (← IO.FS.readFile (directory / "assembly.txt")).splitOn "\n"
  let [_, second, _, _] := nativePaths | throw (IO.userError "expected four native occurrences")
  let native ← load (directory / "native") nativePaths
  let withEmpty ← load (directory / "native") assembledPaths
  let late ← load (directory / "late") nativePaths

  let reorder ← select #[5, 3, 6, 0, 5]
  let empty ← select #[]
  let full := fun manifest => Hive.Manifest.Heterogeneous.read declared {} {} manifest
  let projected := fun manifest position => project declared {} {} manifest position
  save directory "native" (convert declared {} {} {} native) (full native)
  save directory "reordered" (convertProjected declared {} {} {} native reorder) (projected native reorder)
  save directory "with_empty_group" (convert declared {} {} {} withEmpty) (full withEmpty)
  save directory "zero_width" (convertProjected declared {} {} {} withEmpty empty) (projected withEmpty empty)
  save directory "empty_manifest" (convert declared {} {} {} []) (full [])
  save directory "empty_manifest_projected" (convertProjected declared {} {} {} [] empty) (projected [] empty)

  let blocked : Arrow.ObservationLimits := {ipc.fields := 0, ipc.batches := 0}
  match convert declared {} {} blocked native with
  | .error (.writer (.ipc (.limit .batches))) => pure ()
  | _ => throw (IO.userError "writer limit did not reject the clean manifest")
  expectLate second offset (convert declared {} {} {} late)
  expectLate second offset (convert declared {} {} blocked late)
  let omitFailed ← select #[5, 6, 2]
  expectLate second offset (convertProjected declared {} {} blocked late omitFailed)
  expectLate second offset (convertProjected declared {} {} blocked late empty)

  let unsupported : Schema := ⟨#[], ⟨#[⟨"time", .timestamp ⟨⟨.millisecond, none⟩, true⟩, .asNull⟩]⟩⟩
  match convert unsupported {} {} blocked native with
  | .error (.source (.unsupportedPartition "time")) => pure ()
  | _ => throw (IO.userError "source schema refusal was lost")

  let first :: tail := native | throw (IO.userError "native fixture missing")
  let missing := {first with path := "region=a/part.parquet"}
  match convert declared {} {} blocked (first :: missing :: tail) with
  | .error (.source (.file 1 "region=a/part.parquet" (.path (.binding _ (.missingKey "rank"))))) => pure ()
  | _ => throw (IO.userError "reached Hive path failure was lost")
  IO.println "Verified six native IPC readbacks and seven typed refusals"
