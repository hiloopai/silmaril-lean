module

public import Silmaril.Formats.Arrow.StructInt32.Stream.Writer.Defs
import Silmaril.Formats.Arrow.StructInt32.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Writer

open Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.StructInt32.Stream.Writer

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

private theorem emit_exact {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List StructInt32.Stream.Row)} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    serialize limits field batches = .ok wire ∧
      ∃ observed, StructInt32.Stream.read limits wire = .ok observed ∧ Agrees field batches observed := by
  unfold emit at written
  obtain ⟨bytes, serialized, written⟩ := bind_ok written
  cases read : StructInt32.Stream.read limits bytes with
  | error cause => simp [read, Except.mapError, Bind.bind, Except.bind] at written
  | ok observed =>
    simp only [read, Except.mapError, Bind.bind, Except.bind] at written
    split at written
    · rename_i agreement
      cases Except.ok.inj written
      exact ⟨serialized, observed, read, agreement⟩
    · contradiction

theorem emit_readback {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List StructInt32.Stream.Row)} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ observed size,
      StructInt32.Stream.read limits wire = .ok observed ∧ Agrees field batches observed ∧
      wire.wf = true ∧ readEnvelope limits.ipc wire 0 = .ok (.metadata size) ∧
      StructInt32.readSchema limits.ipc (wire.slice 8 size) = .ok field ∧
      StructInt32.Stream.BatchesWire limits field wire limits.ipc.batches 0 (8 + size) observed.batches := by
  obtain ⟨observed, checked, agrees⟩ := (emit_exact written).2
  obtain ⟨wellFormed, size, envelope, schema, records⟩ := StructInt32.Stream.read_wire checked
  rw [agrees.1] at schema records
  exact ⟨observed, size, checked, agrees, wellFormed, envelope, schema, records⟩

theorem emit_frames {limits : ObservationLimits} {field : StructInt32.Field}
    {batches : List (List StructInt32.Stream.Row)} {wire : KBytes}
    (written : emit limits field batches = .ok wire) :
    ∃ schema records, emitSchema limits.ipc field = .ok schema ∧
      (batches.zipIdx.mapM fun (rows, index) =>
        (emitRecord limits.ipc field rows).mapError (Error.record index)) = .ok records ∧
      wire = schema ++ records.foldr (· ++ ·) StreamWriter.eos := by
  have serialized := (emit_exact written).1
  unfold serialize at serialized
  split at serialized
  · contradiction
  · obtain ⟨_, _, serialized⟩ := bind_ok serialized
    obtain ⟨schema, header, serialized⟩ := bind_ok serialized
    obtain ⟨records, frames, serialized⟩ := bind_ok serialized
    exact ⟨schema, records, header, frames, (Except.ok.inj serialized).symm⟩

end Silmaril.Proofs.Formats.Arrow.StructInt32.Stream.Writer
