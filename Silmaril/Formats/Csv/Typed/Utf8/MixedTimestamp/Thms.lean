module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.Correctness
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.Rows
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.Composition
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp

open Arrow.MixedFlat.Timestamp (Stream)

/-- Present values round-trip in their declared type, including signed TIMESTAMP counts. -/
theorem codecs_parsePrint (field : Field) : (codecs field).ParsePrint :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.codecs_parsePrint field

/-- Shared lexical CSV decoding recovers the exact ordered dependent rows at matching bounds. -/
theorem decode_encode {limits : Limits} {schema : Schema} {rows : Table schema Cell}
    {wire : Csv.Bytes} (written : encode limits schema rows = .ok wire) :
    decode limits schema wire = .ok rows :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.decode_encode written

/-- One body step checks the original record and propagates the next failure unchanged.
The record, its typed cells and requiredness must pass before the suffix is visited. -/
theorem readBody_step (schema : Schema) (maximum fuel index : Nat) (b : UInt8) (bs : Csv.Bytes) :
    readBody schema maximum (fuel + 1) index (b :: bs) =
      match Bounded.Internal.readRow (b :: bs) with
      | none => .error (.row index .malformedWire)
      | some (raw, rest) =>
        match Typed.Internal.importRow schema codecs raw with
        | .error cause => .error (.row index cause)
        | .ok row =>
          match checkRow schema index row with
          | .error cause => .error cause
          | .ok () => (readBody schema maximum fuel (index + 1) rest).map (row :: ·) :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.readBody_step schema maximum fuel index b bs

/-- Transposing the one newly constructed batch recovers every flat row. -/
theorem flatten_streamOfRows (fields : List Field) (rows : Table (schemaOf fields) Cell) :
    flatten fields (streamOfRows fields rows).batches = .ok rows :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.flatten_streamOfRows fields rows

/-- Successful CSV output retains the explicit ordered descriptors and flattened rows. -/
theorem fromStream_roundtrip {limits : Limits} {source : Stream} {output : Output}
    (written : fromStream limits source = .ok output) :
    ∃ (rows : Table (schemaOf source.fields) Cell),
      output.fields = source.fields ∧ flatten source.fields source.batches = .ok rows ∧
      decode limits (schemaOf source.fields) output.wire = .ok rows :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.fromStream_roundtrip written

/-- Successful CSV import writes one batch and the checked IPC reader recovers it through EOS. -/
theorem toIpc_readback {csv : Limits} {ipc : Arrow.ObservationLimits} {fields : List Field}
    {wire : Csv.Bytes} {output : KBytes} (written : toIpc csv ipc fields wire = .ok output) :
    ∃ (rows : Table (schemaOf fields) Cell),
      decode csv (schemaOf fields) wire = .ok rows ∧
      Arrow.MixedFlat.Timestamp.read ipc output = .ok (streamOfRows fields rows) ∧
      flatten fields (streamOfRows fields rows).batches = .ok rows :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.toIpc_readback written

/-- The original IPC error precedes every CSV output decision. -/
theorem fromIpc_source_error {ipc : Arrow.ObservationLimits} {csv : Limits} {wire : KBytes}
    {cause : Arrow.MixedFlat.Timestamp.Error} (failed : Arrow.MixedFlat.Timestamp.read ipc wire = .error cause) :
    fromIpc ipc csv wire = .error (.source cause) := by
  simp [fromIpc, failed, Bind.bind, Except.bind, Except.mapError]

/-- The original CSV failure precedes IPC writer admission. -/
theorem toIpc_csv_error {csv : Limits} {ipc : Arrow.ObservationLimits} {fields : List Field}
    {wire : Csv.Bytes} {cause : Error} (failed : decode csv (schemaOf fields) wire = .error cause) :
    toIpc csv ipc fields wire = .error (.csv cause) := by
  simp [toIpc, failed, Bind.bind, Except.bind, Except.mapError]

/-- Successful native IPC to CSV and back preserves the ordered flattened observation. -/
theorem ipc_roundtrip {sourceLimits outputLimits : Arrow.ObservationLimits} {csv : Limits}
    {input output : KBytes} {interchange : Output}
    (exported : fromIpc sourceLimits csv input = .ok interchange)
    (imported : toIpc csv outputLimits interchange.fields interchange.wire = .ok output) :
    ∃ source target : Stream,
      Arrow.MixedFlat.Timestamp.read sourceLimits input = .ok source ∧
      Arrow.MixedFlat.Timestamp.read outputLimits output = .ok target ∧
      RowEquivalent source target :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.ipc_roundtrip exported imported

/-- If the mixed Parquet writer also admits the CSV-reemitted IPC, its ordered projection
has the original flattened rows and the new IPC observation's boundaries. -/
theorem ipc_parquet_roundtrip
    {sourceLimits outputLimits : Arrow.ObservationLimits} {csv : Limits}
    {parquet : Parquet.MixedV1Writer.FromIpc.WithTimestamp.Limits}
    {input output : KBytes} {wire : Silmaril.Formats.Bytes} {interchange : Output}
    (exported : fromIpc sourceLimits csv input = .ok interchange)
    (imported : toIpc csv outputLimits interchange.fields interchange.wire = .ok output)
    (written : Parquet.MixedV1Writer.FromIpc.WithTimestamp.convert outputLimits parquet output = .ok wire) :
    ∃ (source : Stream) (projected : Parquet.FlatProjection.Events.Checked),
      Arrow.MixedFlat.Timestamp.read sourceLimits input = .ok source ∧
      Parquet.FlatProjection.Events.readAll parquet.readback wire
        (Parquet.MixedV1Writer.FromIpc.WithTimestamp.ordinals source) =
          .ok ⟨projected.schema, projected.trace parquet.readback⟩ ∧
      (projected.trace parquet.readback).termination = .eos ∧
      RowEquivalent source (Parquet.FlatProjection.Events.ToIpc.observation (projected.trace parquet.readback)) :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.ipc_parquet_roundtrip exported imported written

/-- At a vacant name, a checked import with the same declaration inserts exactly the decoded rows. -/
theorem NamedTable.importCsv_exact {Name : Type*} [DecidableEq Name]
    {db : NamedTable.Database Name} {name : Name} {fields : List Field} {limits : Limits}
    {wire : Csv.Bytes} {rows : Table (schemaOf fields) Cell} (vacant : db name = none)
    (decoded : decode limits (schemaOf fields) wire = .ok rows) :
    NamedTable.importCsv db name fields fields limits wire =
      .ok (Function.update db name (some ⟨schemaOf fields, rows⟩)) := by
  apply (Relational.NamedTable.importCollected_ok_iff _ _ _ _ _).mpr
  exact ⟨vacant, rows, by simp [decoded, Except.map], rfl⟩

/-- Successful named export round-trips the exact stored schema and rows. -/
theorem NamedTable.exportCsv_roundtrip {Name : Type*} {db : NamedTable.Database Name} {name : Name}
    {fields : List Field} {limits : Limits} {output : Output}
    (written : NamedTable.exportCsv db name fields limits = .ok output) :
    ∃ (rows : Table (schemaOf fields) Cell),
      Silmaril.Relational.Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      output.fields = fields ∧ decode limits (schemaOf fields) output.wire = .ok rows :=
  Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.namedExport_roundtrip written

end Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp
