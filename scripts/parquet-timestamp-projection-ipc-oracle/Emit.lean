module

import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc.Defs

open Silmaril Silmaril.Formats
open Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf.Projection.ToIpc

private def load (directory : System.FilePath) (name : String) : IO Bytes :=
  (IO.FS.readBinFile (directory / (name ++ ".parquet"))).map fun raw => ⟨raw⟩

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
  let observed ← require (Arrow.TimestampStream.Ordered.read {} wire)
  unless observed.fields.length == ordinals.size && observed.batches.map (·.rowCount) == rows do
    throw (IO.userError s!"{name}: observed IPC batch shape differs")
  expectError name (.batch rows.length .trailingBytes)
    (Arrow.TimestampStream.Ordered.read {} (wire ++ KBytes.leaf 1 0))
  IO.FS.writeBinFile (directory / (name ++ ".arrows")) wire.toByteArray

private def checkNative (directory : System.FilePath) : IO Unit := do
  let raw ← IO.FS.readBinFile (directory / "native_ordered.arrow")
  let wire := KBytes.ofChunks 1 raw.size (raw.data.toList.map UInt8.toNat)
  let observed ← require (Arrow.TimestampStream.Ordered.read {} wire)
  let utc : Arrow.TimestampBatch.Binding := ⟨"utc_ms", true, ⟨.millisecond, some "UTC"⟩⟩
  let localField : Arrow.TimestampBatch.Binding := ⟨"local_us", false, ⟨.microsecond, none⟩⟩
  let expected : Arrow.TimestampStream.Ordered.Stream :=
    ⟨[utc, localField, utc],
      [⟨3, [[some (-9223372036854775808), none, some 9223372036854775807],
            [some 1, some (-2), some 0], [none, some 0, some (-1)]]⟩, ⟨0, [[], [], []]⟩]⟩
  unless observed = expected do
    throw (IO.userError "native PyArrow positional metadata, counts or row counts differed")

private def writerControls : IO Unit := do
  let field : Arrow.TimestampBatch.Binding := ⟨"t", false, ⟨.nanosecond, none⟩⟩
  let test := Arrow.TimestampStream.Ordered.Writer.emit
  expectError "column count" (.record 0 (.columnCount 1 0)) (test {} [field] [⟨1, []⟩])
  expectError "row count" (.record 0 (.rowCount 0 1 0)) (test {} [field] [⟨1, [[]]⟩])
  expectError "required-column null" (.record 0 (.requiredNull 0)) (test {} [field] [⟨1, [[none]]⟩])
  expectError "signed Int64 overflow" (.record 0 (.payload 0 .outOfRange))
    (test {} [field] [⟨1, [[some 9223372036854775808]]⟩])
  expectError "named timezone" (.timezone 0 (some "Europe/Berlin"))
    (test {} [{field with metadata.timezone := some "Europe/Berlin"}] [])
  expectError "zero-width positive row budget" (.ipc (.limit .totalRows)) (test { totalRows := 2 } [] [⟨3, []⟩])

public def main (args : List String) : IO Unit := do
  let [folder, offset, declared, actual] := args | throw (IO.userError "expected fixture folder and CRC evidence")
  let [some offset, some declared, some actual] := [offset, declared, actual].map String.toNat? |
    throw (IO.userError "invalid independent CRC evidence")
  let directory : System.FilePath := folder
  emit directory "native_v1" "duplicate_v1" #[4, 2, 3, 2] [512, 508, 512]
  emit directory "native_v2" "reordered_v2" #[3, 4, 2] [512, 508, 512]
  emit directory "native_v1" "zero_width" #[] [512, 508, 512]
  emit directory "native_schema_only" "schema_only" #[3, 2] []
  emit directory "assembled_framed_zero" "explicit_zero_row" #[4, 2, 3, 2] [512, 0, 508]
  emit directory "assembled_framed_zero" "zero_width_with_zero_row" #[] [512, 0, 508]
  emit directory "mutated_late_local_dictionary_crc" "omit_corrupt" #[4, 2] [512, 508, 512]
  let bad ← load directory "mutated_late_local_dictionary_crc"
  let failure : Leaf.Projection.ToIpc.Error := .source
    (.read 1 1 3 (.v1 .zstd (.checksum 0 offset (.mismatch declared.toUInt32 actual.toUInt32))))
  expectError "late source CRC" failure (convert {} {} bad #[4, 3, 2])
  expectError "late source CRC before writer limits" failure
    (convert {} { ipc.batches := 0, ipc.fields := 0 } bad #[4, 3, 2])
  checkNative directory
  writerControls
  IO.println "Certified seven Lean IPC streams, independent PyArrow input, positional alignment, EOS and late source precedence"
