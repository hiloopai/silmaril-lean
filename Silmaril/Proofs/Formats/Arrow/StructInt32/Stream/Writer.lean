module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs
import Silmaril.Formats.Arrow.StructInt32.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Writer

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.StructInt32 (RightWidth)
open Silmaril.Formats.Arrow.StructInt32.Stream (RowFor)
open Silmaril.Formats.Arrow.StructInt32.Stream.Writer

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem emit_exact {width : RightWidth} {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List (RowFor width.Value))} {wire : KBytes}
    (written : emitFor width limits field batches = .ok wire) :
    serializeFor width limits field batches = .ok wire ∧
      ∃ observed, StructInt32.Stream.readFor width limits wire = .ok observed ∧ AgreesFor field batches observed := by
  unfold emitFor at written
  obtain ⟨bytes, serialized, written⟩ := bind_ok written
  cases read : StructInt32.Stream.readFor width limits bytes with
  | error cause => simp [read, Except.mapError, Bind.bind, Except.bind] at written
  | ok observed =>
    simp only [read, Except.mapError, Bind.bind, Except.bind] at written
    split at written
    · rename_i agreement
      cases Except.ok.inj written
      exact ⟨serialized, observed, read, agreement⟩
    · contradiction

theorem emitFor_readback {width : RightWidth} {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List (RowFor width.Value))} {wire : KBytes}
    (written : emitFor width limits field batches = .ok wire) :
    ∃ observed size,
      StructInt32.Stream.readFor width limits wire = .ok observed ∧ AgreesFor field batches observed ∧
      wire.wf = true ∧ readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      StructInt32.readSchemaFor width limits.ipc (wire.slice 8 size) = .ok field ∧
      StructInt32.Stream.BatchesWireFor width limits field wire limits.ipc.batches 0 (8 + size) observed.batches := by
  obtain ⟨observed, checked, agrees⟩ := (emit_exact written).2
  obtain ⟨wellFormed, size, envelope, schema, records⟩ := StructInt32.Stream.readFor_wire checked
  rw [agrees.1] at schema records
  exact ⟨observed, size, checked, agrees, wellFormed, envelope, schema, records⟩

theorem emitFor_frames {width : RightWidth} {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List (RowFor width.Value))} {wire : KBytes}
    (written : emitFor width limits field batches = .ok wire) :
    ∃ schema records, emitSchemaFor width limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) =>
        (emitRecordFor width limits.ipc field rows).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos := by
  have serialized := (emit_exact written).1
  unfold serializeFor at serialized
  split at serialized
  · contradiction
  · obtain ⟨_, _, serialized⟩ := bind_ok serialized
    obtain ⟨schema, header, serialized⟩ := bind_ok serialized
    obtain ⟨records, frames, serialized⟩ := bind_ok serialized
    exact ⟨schema, records, header, frames, (Except.ok.inj serialized).symm⟩

end Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Writer
