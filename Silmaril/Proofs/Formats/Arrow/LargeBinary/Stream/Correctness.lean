module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
import Silmaril.Formats.Arrow.LargeBinary.Thms
import Silmaril.Formats.Arrow.Binary.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow
open LargeBinary.Stream

theorem readRecord_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {offset size : Nat} {record : Batch}
    (read : readRecord limits framing input field offset size = .ok record) :
    RecordWire limits framing input field offset size record := by
  unfold readRecord at read
  cases parsed : Arrow.readMessage limits (input.slice (offset + framing.prefixSize) size) with
  | error cause => simp [parsed, Except.mapError, Bind.bind, Except.bind] at read
  | ok message =>
    obtain ⟨header, bodyLength⟩ := message
    cases header with
    | schema fields => simp [parsed, Except.mapError, Bind.bind, Except.bind] at read
    | recordBatch metadata =>
      let range : Range := ⟨offset, framing.prefixSize, size, bodyLength⟩
      cases bodyEq : Arrow.readBody limits input range.bodyStart bodyLength with
      | error cause =>
        simp [parsed, bodyEq, range, Except.mapError, Bind.bind, Except.bind] at read
      | ok body =>
        cases bound : Binary.bindBody limits metadata body with
        | error cause =>
          simp [parsed, bodyEq, range, bound, Except.mapError, Bind.bind, Except.bind] at read
        | ok physical =>
          obtain ⟨node, buffers⟩ := physical
          cases column : LargeBinary.readColumn limits field.nullable node buffers with
          | error cause =>
            simp [parsed, bodyEq, range, bound, column, Except.mapError, Bind.bind, Except.bind] at read
          | ok values =>
            simp only [parsed, bodyEq, range, bound, column, Except.mapError, Bind.bind,
              Except.bind] at read
            cases read
            obtain ⟨_, _, _, within, rfl⟩ := (Arrow.readBody_iff _ _ _ _ _).mp bodyEq
            exact ⟨rfl, within, metadata, node, buffers, parsed, Binary.bindBody_sound bound,
              LargeBinary.readColumn_sound column⟩

private theorem readBatches_sound {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {remaining ordinal offset : Nat} {records : List Batch} {eos : Nat}
    (read : readBatches limits framing input field remaining ordinal offset = .ok (records, eos)) :
    BatchesWire limits framing input field remaining offset records eos := by
  rw [readBatches] at read
  cases framed : framing.readEnvelope limits input offset with
  | error cause => simp [framed, Except.mapError, Bind.bind, Except.bind] at read
  | ok envelope =>
    cases envelope with
    | eos =>
      by_cases full : offset + framing.prefixSize = input.len
      · simp [framed, full, Except.mapError, Bind.bind, Except.bind] at read
        obtain ⟨rfl, rfl⟩ := read
        exact .eos framed full
      · simp [framed, full, Except.mapError, Bind.bind, Except.bind] at read
    | metadata size =>
      cases remaining with
      | zero => simp [framed, Except.mapError, Bind.bind, Except.bind] at read
      | succ fuel =>
        cases batchEq : readRecord limits framing input field offset size with
        | error cause => simp [framed, batchEq, Except.mapError, Bind.bind, Except.bind] at read
        | ok batch =>
          cases suffix : readBatches limits framing input field fuel (ordinal + 1) batch.range.next with
          | error cause =>
            simp [framed, batchEq, suffix, Except.mapError, Bind.bind, Except.bind] at read
          | ok result =>
            obtain ⟨rest, stop⟩ := result
            simp [framed, batchEq, suffix, Except.mapError, Bind.bind, Except.bind,
              Pure.pure, Except.pure] at read
            obtain ⟨rfl, rfl⟩ := read
            exact .more framed (readRecord_sound batchEq) (readBatches_sound suffix)
termination_by remaining

private theorem schema_frame {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {start : Nat}
    (read : readSchemaFrame limits framing input = .ok (field, start)) :
    ∃ size, framing.readEnvelope limits input 0 = .ok (.metadata size) ∧
      LargeBinary.readSchema limits (input.slice framing.prefixSize size) = .ok field ∧
      start = framing.prefixSize + size := by
  unfold readSchemaFrame at read
  cases framed : framing.readEnvelope limits input 0 with
  | error cause => simp [framed, Except.mapError, Bind.bind, Except.bind] at read
  | ok envelope =>
    cases envelope with
    | eos => simp [framed, Except.mapError, Bind.bind, Except.bind] at read
    | metadata size =>
      cases parsed : LargeBinary.readSchema limits (input.slice framing.prefixSize size) with
      | error cause => simp [framed, parsed, Except.mapError, Bind.bind, Except.bind] at read
      | ok actual =>
        simp [framed, parsed, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at read
        obtain ⟨rfl, rfl⟩ := read
        exact ⟨size, rfl, parsed, rfl⟩

theorem read_sound {limits : Limits} {framing : Framing} {input : KBytes} {observed : Observed}
    (success : read limits framing input = .ok observed) : StreamWire limits framing input observed := by
  unfold LargeBinary.Stream.read at success
  cases wf : input.wf
  · simp [wf] at success
  · simp only [wf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
    cases header : readSchemaFrame limits framing input with
    | error cause => simp [header, Except.mapError, Bind.bind, Except.bind] at success
    | ok schema =>
      obtain ⟨field, start⟩ := schema
      cases batchesEq : readBatches limits framing input field limits.batches 0 start with
      | error cause => simp [header, batchesEq, Except.mapError, Bind.bind, Except.bind] at success
      | ok result =>
        obtain ⟨records, eos⟩ := result
        simp only [header, batchesEq, Except.mapError, Bind.bind, Except.bind] at success
        cases success
        obtain ⟨size, envelope, parsed, rfl⟩ := schema_frame header
        exact ⟨wf, size, envelope, parsed, readBatches_sound batchesEq⟩

theorem record_octets {limits : Limits} {framing : Framing} {input : KBytes}
    {field : LargeBinary.Field} {offset size : Nat} {record : Batch}
    (wf : input.wf = true) (wire : RecordWire limits framing input field offset size record) :
    let range := record.range
    range.next ≤ input.len ∧
      (input.slice range.metadataStart range.metadataSize).toList =
        (input.toList.drop range.metadataStart).take range.metadataSize ∧
      (input.slice range.bodyStart range.bodyLength).toList =
        (input.toList.drop range.bodyStart).take range.bodyLength := by
  obtain ⟨_, within, _⟩ := wire
  refine ⟨within, KBytes.toList_slice _ _ _ wf ?_, KBytes.toList_slice _ _ _ wf within⟩
  have extent : record.range.metadataStart + record.range.metadataSize + record.range.bodyLength ≤
      input.len := within
  omega

end Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream
