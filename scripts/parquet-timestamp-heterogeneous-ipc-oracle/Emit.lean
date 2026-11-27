module

import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs
meta import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc

private def load (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

private def loadIpc (directory : System.FilePath) (name : String) : IO KBytes := do
  let raw ← IO.FS.readBinFile (directory / (name ++ ".arrow"))
  return KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)

private def require {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error cause => throw (IO.userError s!"{repr cause}")

private def expectError {ε α : Type} [DecidableEq ε] [Repr ε]
    (label : String) (expected : ε) (result : Except ε α) : IO Unit :=
  match result with
  | .error actual =>
    unless actual = expected do
      throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input was accepted")

private def emit (directory : System.FilePath) (source name : String) (ordinals : Array Nat)
    (rows : List Nat) : IO Unit := do
  let bytes ← load directory source
  let wire ← require (convert {} {} bytes ordinals)
  let observed ← require (Arrow.MixedFlat.Timestamp.read {} wire)
  unless observed.fields.length == ordinals.size && observed.batches.map (·.rowCount) == rows do
    throw (IO.userError s!"{name}: observed IPC batch shape differs")
  expectError name (.batch rows.length .trailingBytes)
    (Arrow.MixedFlat.Timestamp.read {} (wire ++ KBytes.leaf 1 0))
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def checkNative (directory : System.FilePath) : IO Unit := do
  let label : Arrow.MixedFlat.Timestamp.Field := ⟨"label", true, .utf8⟩
  let seconds : Arrow.MixedFlat.Timestamp.Field := ⟨"local_seconds", false, .timestamp ⟨.second, none⟩⟩
  let utc : Arrow.MixedFlat.Timestamp.Field := ⟨"utc_ns", true, .timestamp ⟨.nanosecond, some "UTC"⟩⟩
  let code : Arrow.MixedFlat.Timestamp.Field := ⟨"code", false, .int32⟩
  let expected : Arrow.MixedFlat.Timestamp.Stream := ⟨[seconds, label, utc, code, label],
    [⟨3, [.timestamp [some 9223372036854775807, some (-9223372036854775808), some (-1)],
          .utf8 [some "原", none, some ""],
          .timestamp [some (-9223372036854775808), some 9223372036854775807, none],
          .int32 [some (-2147483648), some 0, some 2147483647], .utf8 [none, some "🙂", some "second label"]]⟩,
     ⟨0, [.timestamp [], .utf8 [], .timestamp [], .int32 [], .utf8 []]⟩]⟩
  let zeroWidth : Arrow.MixedFlat.Timestamp.Stream := ⟨[], [⟨4, []⟩, ⟨0, []⟩, ⟨2, []⟩]⟩
  for (name, expected) in [("native_mixed", expected), ("native_zero_width", zeroWidth)] do
    let wire ← loadIpc directory name
    let observed ← require (Arrow.MixedFlat.Timestamp.read {} wire)
    unless observed = expected do
      throw (IO.userError s!"{name}: native IPC positional metadata, cells or batch counts differed")
    let encoded ← require (Arrow.MixedFlat.Timestamp.Writer.emit {} observed)
    IO.FS.writeBinFile (directory / (name ++ ".arrows")) encoded.toByteArray
  let trailing ← loadIpc directory "mutated_ipc_trailing"
  expectError "native trailing bytes" (.batch 2 .trailingBytes) (Arrow.MixedFlat.Timestamp.read {} trailing)
  let zone ← loadIpc directory "native_named_timezone"
  expectError "native named timezone" (.timezone 0 (some "Europe/Berlin")) (Arrow.MixedFlat.Timestamp.read {} zone)
  let empty ← loadIpc directory "native_zero_width"
  expectError "aggregate row cap at width zero" (.batch 2 (.budget (.limit .totalRows)))
    (Arrow.MixedFlat.Timestamp.read {totalRows := 4} empty)

private def writerControls : IO Unit := do
  let field : Arrow.MixedFlat.Timestamp.Field := ⟨"time", false, .timestamp ⟨.nanosecond, none⟩⟩
  let test := Arrow.MixedFlat.Timestamp.Writer.emit
  expectError "column count" (.record 0 (.columnCount 1 0)) (test {} ⟨[field], [⟨1, []⟩]⟩)
  expectError "column type" (.record 0 (.columnType 0)) (test {} ⟨[field], [⟨1, [.int32 [some 0]]⟩]⟩)
  expectError "timestamp row count" (.record 0 (.timestamp (.rowCount 0 1 0)))
    (test {} ⟨[field], [⟨1, [.timestamp []]⟩]⟩)
  expectError "required null" (.record 0 (.timestamp (.requiredNull 0)))
    (test {} ⟨[field], [⟨1, [.timestamp [none]]⟩]⟩)
  expectError "signed overflow" (.record 0 (.timestamp (.payload 0 .outOfRange)))
    (test {} ⟨[field], [⟨1, [.timestamp [some 9223372036854775808]]⟩]⟩)
  expectError "body cap" (.record 0 (.ipc (.limit .bodyBytes)))
    (test {ipc.bodyBytes := 8} ⟨[field], [⟨1, [.timestamp [some 0]]⟩]⟩)
  expectError "empty projection row cap" (.ipc (.limit .totalRows))
    (test {totalRows := 0} ⟨[], [⟨1, []⟩]⟩)

public def main (args : List String) : IO Unit := do
  let [folder, offset] := args | throw (IO.userError "expected fixture folder and dictionary offset")
  let some offset := offset.toNat? | throw (IO.userError "invalid dictionary offset")
  let directory : System.FilePath := folder
  emit directory "native_v1" "duplicate_v1" #[3, 0, 1, 2, 1] [5, 3, 2]
  emit directory "native_v2" "reordered_v2" #[2, 1, 0, 3] [5, 3, 2]
  emit directory "native_v1" "zero_width" #[] [5, 3, 2]
  emit directory "native_schema_only" "schema_only" #[2, 0, 1] []
  emit directory "assembled_framed_zero" "explicit_zero_row" #[1, 2, 0, 3, 2] [5, 0, 3]
  emit directory "assembled_framed_zero" "zero_width_with_zero_row" #[] [5, 0, 3]
  emit directory "mutated_late_timestamp_dictionary_magic" "omit_corrupt" #[1, 3, 0] [5, 3, 2]
  let bad ← load directory "mutated_late_timestamp_dictionary_magic"
  let failure : Error := .source (.column 1 3 2 (.timestamp
    (.v1 .zstd (.decode 0 offset (.frame (.frame .badMagic))))))
  let ordinals := #[3, 0, 1, 2, 1]
  expectError "late source dictionary failure" failure (convert {} {} bad ordinals)
  let blocked : Arrow.ObservationLimits := {ipc.fields := 0, ipc.batches := 0, totalRows := 0}
  expectError "late source failure before writer admission" failure (convert {} blocked bad ordinals)
  let clean ← load directory "native_v1"
  expectError "writer admission after clean source" (.writer (.ipc (.limit .batches)))
    (convert {} blocked clean ordinals)
  checkNative directory
  writerControls
  IO.println "Certified seven projection streams, genuine mixed and zero-width IPC input, and typed refusals"
