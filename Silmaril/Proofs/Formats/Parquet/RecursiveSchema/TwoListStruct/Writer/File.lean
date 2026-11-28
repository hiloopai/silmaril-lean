module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.TwoListStruct (Plan)
open Parquet.RecursiveSchema.TwoListStruct.Writer
open Parquet.RecursiveSchema.TwoListStruct.Reader (readAll readAll_wire)
open Parquet.RecursiveSchema.Repeated.Writer.Schema (equal_exact)

/-- The original footer records the two consecutive frame starts, both
slot counts and both header-inclusive sizes for each column. -/
public theorem footer_exact {limits : Limits} {checksum : Bool} {plan : Plan} {offset priorSlots : Nat}
    {input : Arrow.RecursiveSchema.Batch.Rows.Observation} {output : WrittenGroup}
    (wire : GroupWire limits checksum plan offset priorSlots input output) :
    ∃ left right : Footer.ColumnChunk,
    (output.index plan).metadata.numRows = (input.rowCount : Int) ∧
    (output.index plan).metadata.columns = [left, right] ∧
    left.metadata.dataPageOffset = (offset : Int) ∧
    right.metadata.dataPageOffset = (output.middle offset : Int) ∧
    left.metadata.numValues = (output.left.slots : Int) ∧
    right.metadata.numValues = (output.right.slots : Int) ∧
    left.metadata.totalCompressedSize = (output.left.page.wire.length : Int) ∧
    left.metadata.totalUncompressedSize = (output.left.page.wire.length : Int) ∧
    right.metadata.totalCompressedSize = (output.right.page.wire.length : Int) ∧
    right.metadata.totalUncompressedSize = (output.right.page.wire.length : Int) := by
  obtain ⟨_, _, _, _, first, second⟩ := wire.projected
  refine ⟨_, _, congrArg Int.ofNat first.rows, rfl, congrArg Int.ofNat first.atOffset,
    congrArg Int.ofNat second.atOffset, rfl, rfl, rfl, rfl, rfl, rfl⟩

public theorem serialize_construction {limits : Limits} {input : Input} {output : Output}
    (built : serialize limits input = .ok output) : Construction limits input output := by
  unfold serialize at built
  cases original : build limits input with
  | error => simp [original, Except.map] at built
  | ok file =>
    have same : file.val = output := by simpa [original, Except.map] using built
    exact same ▸ file.property

public theorem certify_readback {limits : Limits} {input : Input} {output : Output}
    (accepted : certify limits input output = .ok ()) : Readback limits input output := by
  unfold certify at accepted
  cases original : Parquet.RecursiveSchema.TwoListStruct.openFile limits.schema.snapshot output.bytes with
  | error => simp [original, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
    cases same : agrees limits input output source with
    | false => simp [original, same, Except.mapError, bind, Except.bind] at accepted
    | true =>
      cases rows : readAll limits.chunk source.schema with
      | error => simp [original, same, rows, Except.mapError, bind, Except.bind] at accepted
      | ok recovered =>
        have batches : recovered.isEqv input.groups
            (Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth) = true := by
          simpa [original, same, rows, Except.mapError, bind, Except.bind, pure, Except.pure] using accepted
        obtain ⟨count, pairs⟩ := (List.isEqv_eq_true_iff_getElem _).mp batches
        have exactBatches := List.ext_getElem count fun i hi _ =>
          Arrow.RecursiveSchema.Batch.Writer.agrees_exact (pairs i hi)
        rw [exactBatches] at rows
        simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at same
        exact ⟨source, original, source.bytes_exact, same.2.1, same.2.2.1,
          equal_exact same.1, same.2.2.2, rows, readAll_wire rows⟩

public theorem emit_wire {limits : Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) : Construction limits input output ∧ Readback limits input output := by
  unfold emit at written
  cases built : serialize limits input with
  | error => simp [built, bind, Except.bind] at written
  | ok file =>
    cases accepted : certify limits input file with
    | error => simp [built, accepted, bind, Except.bind] at written
    | ok confirmed =>
      cases confirmed
      have same : file = output := by simpa [built, accepted, bind, Except.bind, pure, Except.pure] using written
      exact same ▸ ⟨serialize_construction built, certify_readback accepted⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Writer
