module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc.Defs
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc

open Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Arrow.BinaryView
open Date32.Utf8.ManifestWriter
open Date32.Utf8.ManifestWriter.ToIpc
open Int32ByteArrayGroup.File (Value)

theorem groups_rowCounts (layout : Schema) (trace : Trace layout) :
    (groups layout trace).map List.length = trace.batches.map (·.rowCount) := by
  unfold groups
  generalize trace.batches = batches
  induction batches with
  | nil => rfl
  | cons batch rest ih => exact congrArg₂ List.cons (batch.length_eq (0 : Fin 1)) ih

theorem convert_outcome (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : Arrow.Limits) (view : Column.Limits) (keep : Scan.Predicate layout.keys.schema.toScan Value)
    (files : List File) :
    convert layout options limits ipc view keep files =
      match readSelected layout options limits (projection layout) keep files with
      | .error cause => .error (.admission cause)
      | .ok trace =>
        match trace.termination with
        | .eos =>
          let source := binarySource layout trace
          (Silmaril.Formats.Arrow.BinaryView.StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer
        | outcome => .error (.source outcome) := by
  cases read : readSelected layout options limits (projection layout) keep files <;>
    simp only [convert, read, Except.mapError, Bind.bind, Except.bind]
  rfl

theorem encodeTrace_readback {layout : Schema} {ipc : Arrow.Limits} {view : Column.Limits}
    {trace : Trace layout} {wire : KBytes} (written : encodeTrace layout ipc view trace = .ok wire) :
    trace.termination = .eos ∧ ∃ batches : List (List (Option KBytes)),
      Silmaril.Formats.Arrow.BinaryView.Stream.read ipc view wire = .ok ⟨⟨layout.byteName, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) =
        (groups layout trace).map (List.map (Option.map Bytes.toList)) := by
  cases terminal : trace.termination <;> simp [encodeTrace, terminal] at written
  let source := binarySource layout trace
  change (Silmaril.Formats.Arrow.BinaryView.StreamWriter.emit ipc view ⟨layout.byteName, true, .binary⟩ source.batches).mapError
    Error.writer = .ok wire at written
  cases emitted : Silmaril.Formats.Arrow.BinaryView.StreamWriter.emit ipc view ⟨layout.byteName, true, .binary⟩ source.batches with
  | error cause => simp [emitted, Except.mapError] at written
  | ok bytes =>
    have same : bytes = wire := by simpa [emitted, Except.mapError] using written
    subst bytes
    obtain ⟨batches, read, values⟩ := Silmaril.Formats.Arrow.BinaryView.StreamWriter.emit_binary_readback emitted
    exact ⟨rfl, batches, read, values.trans (Plain.ByteArray.ToIpc.batches_octets source)⟩

theorem convert_readback {layout : Schema} {options : PartitionPath.Options} {limits : Limits}
    {ipc : Arrow.Limits} {view : Column.Limits} {keep : Scan.Predicate layout.keys.schema.toScan Value}
    {files : List File} {wire : KBytes} (written : convert layout options limits ipc view keep files = .ok wire) :
    ∃ (trace : Trace layout) (batches : List (List (Option KBytes))),
      readSelected layout options limits (projection layout) keep files = .ok trace ∧
      trace.termination = .eos ∧
      Silmaril.Formats.Arrow.BinaryView.Stream.read ipc view wire = .ok ⟨⟨layout.byteName, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) =
        (groups layout trace).map (List.map (Option.map Bytes.toList)) := by
  cases read : readSelected layout options limits (projection layout) keep files with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok trace =>
    have encoded : encodeTrace layout ipc view trace = .ok wire := by
      simpa [convert, read, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨eos, batches, observed, values⟩ := encodeTrace_readback encoded
    exact ⟨trace, batches, rfl, eos, observed, values⟩

end Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc
