module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Thms
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.Rows

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp

open Silmaril.Formats
open Csv.Typed.Utf8.MixedTimestamp

theorem codecs_parsePrint (field : Field) : (codecs field).ParsePrint := by
  obtain ⟨_, nullable, kind⟩ := field
  cases kind with
  | int32 => exact Csv.Typed.Codecs.int32_parsePrint
  | utf8 => exact Csv.Typed.Utf8.string_parsePrint
  | timestamp metadata =>
    exact Arrow.TimestampStream.ToCsv.codecs_parsePrint ⟨metadata.unit, metadata.timezone, nullable⟩

private theorem readBody_ok (schema : Schema) (maximum fuel index : Nat) (wire : Csv.Bytes)
    (rows : Csv.Typed.Table schema Cell)
    (parsed : Csv.Typed.Utf8.Bounded.Internal.readBody schema codecs fuel wire = .ok rows)
    (required : checkRows schema index rows = .ok ()) :
    readBody schema maximum fuel index wire = .ok rows := by
  induction fuel generalizing index wire rows with
  | zero =>
    cases wire with
    | nil => simpa [Csv.Typed.Utf8.Bounded.Internal.readBody, readBody] using parsed
    | cons b bs => simp [Csv.Typed.Utf8.Bounded.Internal.readBody] at parsed
  | succ fuel ih =>
    cases wire with
    | nil => simpa [Csv.Typed.Utf8.Bounded.Internal.readBody, readBody] using parsed
    | cons b bs =>
      cases record : Csv.Typed.Utf8.Bounded.Internal.readRow (b :: bs) with
      | none => simp [Csv.Typed.Utf8.Bounded.Internal.readBody, record] at parsed
      | some pair =>
        obtain ⟨raw, rest⟩ := pair
        cases decoded : Csv.Typed.Internal.importRow schema codecs raw with
        | error cause => simp [Csv.Typed.Utf8.Bounded.Internal.readBody, record, decoded] at parsed
        | ok row =>
          cases more : Csv.Typed.Utf8.Bounded.Internal.readBody schema codecs fuel rest with
          | error cause =>
            simp [Csv.Typed.Utf8.Bounded.Internal.readBody, record, decoded, more, Except.map] at parsed
          | ok tail =>
            simp [Csv.Typed.Utf8.Bounded.Internal.readBody, record, decoded, more, Except.map] at parsed
            subst rows
            cases valid : checkRow schema index row with
            | error cause => simp [checkRows, valid, Bind.bind, Except.bind] at required
            | ok _ =>
              have checked := ih (index + 1) rest tail more
                (by simpa [checkRows, valid, Bind.bind, Except.bind] using required)
              simp [readBody, record, decoded, valid, checked, Except.mapError, Bind.bind, Except.bind,
                Except.map]

theorem decode_encode {limits : Limits} {schema : Schema} {rows : Csv.Typed.Table schema Cell}
    {wire : Csv.Bytes} (written : encode limits schema rows = .ok wire) :
    decode limits schema wire = .ok rows := by
  cases declared : checkSchema schema with
  | error cause => simp [encode, declared, Bind.bind, Except.bind] at written
  | ok _ =>
    by_cases over : rows.length > limits.maxRows
    · simp [encode, declared, over, Bind.bind, Except.bind, throw] at written
    · cases required : checkRows schema 0 rows with
      | error cause => simp [encode, declared, required, over, Bind.bind, Except.bind] at written
      | ok _ =>
        cases printed : Csv.Typed.Utf8.encode schema codecs rows with
        | error cause =>
          simp [encode, declared, required, printed, over, Bind.bind, Except.bind, Except.mapError] at written
        | ok bytes =>
          simp only [encode, declared, required, printed, over, Bind.bind, Except.bind, Except.mapError,
            ite_false, pure, Except.pure] at written
          split at written
          next => contradiction
          next bounded =>
            cases written
            have parsed := (Csv.Typed.Utf8.Bounded.decode_ok_iff schema codecs limits.maxRows wire rows).mpr
              ⟨Csv.Typed.Utf8.decode_encode codecs_parsePrint printed, Nat.le_of_not_gt over⟩
            cases wire with
            | nil => simp [Csv.Typed.Utf8.Bounded.decode] at parsed
            | cons b bs =>
              cases record : Csv.Typed.Utf8.Bounded.Internal.readRow (b :: bs) with
              | none => simp [Csv.Typed.Utf8.Bounded.decode, record] at parsed
              | some pair =>
                obtain ⟨raw, rest⟩ := pair
                by_cases header : raw = Csv.Typed.header schema
                · simp [Csv.Typed.Utf8.Bounded.decode, record, header] at parsed
                  simp only [decode, bounded, ite_false, declared, record, header, ite_true, Bind.bind,
                    Except.bind]
                  exact readBody_ok _ _ _ _ _ _ parsed required
                · simp [Csv.Typed.Utf8.Bounded.decode, record, header] at parsed

theorem fromStream_roundtrip {limits : Limits} {source : Arrow.MixedFlat.Timestamp.Stream}
    {output : Output} (written : fromStream limits source = .ok output) :
    ∃ (rows : Csv.Typed.Table (schemaOf source.fields) Cell),
      output.fields = source.fields ∧ flatten source.fields source.batches = .ok rows ∧
      decode limits (schemaOf source.fields) output.wire = .ok rows := by
  unfold fromStream at written
  split at written
  next => contradiction
  next =>
    cases flattened : flatten source.fields source.batches with
    | error cause => simp [flattened, Bind.bind, Except.bind, Except.mapError] at written
    | ok rows =>
      cases encoded : encode limits (schemaOf source.fields) rows with
      | error cause => simp [flattened, encoded, Bind.bind, Except.bind, Except.mapError] at written
      | ok wire =>
        simp [flattened, encoded, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at written
        subst output
        exact ⟨rows, rfl, rfl, decode_encode encoded⟩

theorem toIpc_readback {csv : Limits} {ipc : Arrow.ObservationLimits} {fields : List Field}
    {wire : Csv.Bytes} {output : KBytes} (written : toIpc csv ipc fields wire = .ok output) :
    ∃ (rows : Csv.Typed.Table (schemaOf fields) Cell),
      decode csv (schemaOf fields) wire = .ok rows ∧
      Arrow.MixedFlat.Timestamp.read ipc output = .ok (streamOfRows fields rows) ∧
      flatten fields (streamOfRows fields rows).batches = .ok rows := by
  cases decoded : decode csv (schemaOf fields) wire with
  | error cause => simp [toIpc, decoded, Bind.bind, Except.bind, Except.mapError] at written
  | ok rows =>
    cases emitted : Arrow.MixedFlat.Timestamp.Writer.emit ipc (streamOfRows fields rows) with
    | error cause => simp [toIpc, decoded, emitted, Bind.bind, Except.bind, Except.mapError] at written
    | ok bytes =>
      simp [toIpc, decoded, emitted, Bind.bind, Except.bind, Except.mapError] at written
      subst bytes
      exact ⟨rows, rfl, Arrow.MixedFlat.Timestamp.Writer.emit_readback emitted,
        flatten_streamOfRows fields rows⟩

theorem readBody_step (schema : Schema) (maximum fuel index : Nat) (b : UInt8)
    (bs : Csv.Bytes) :
    readBody schema maximum (fuel + 1) index (b :: bs) =
      match Csv.Typed.Utf8.Bounded.Internal.readRow (b :: bs) with
      | none => .error (.row index .malformedWire)
      | some (raw, rest) =>
        match Csv.Typed.Internal.importRow schema codecs raw with
        | .error cause => .error (.row index cause)
        | .ok row =>
          match checkRow schema index row with
          | .error cause => .error cause
          | .ok () => (readBody schema maximum fuel (index + 1) rest).map (row :: ·) := by
  cases record : Csv.Typed.Utf8.Bounded.Internal.readRow (b :: bs) with
  | none => simp only [readBody, record]; rfl
  | some pair =>
    obtain ⟨raw, rest⟩ := pair
    cases decoded : Csv.Typed.Internal.importRow schema codecs raw with
    | error cause => simp [readBody, record, decoded, Bind.bind, Except.bind, Except.mapError]
    | ok row =>
      cases valid : checkRow schema index row with
      | error cause => simp [readBody, record, decoded, valid, Bind.bind, Except.bind, Except.mapError]
      | ok value =>
        cases value
        simp [readBody, record, decoded, valid, Bind.bind, Except.bind, Except.mapError]

theorem fromIpc_roundtrip {ipc : Arrow.ObservationLimits} {csv : Limits} {input : KBytes}
    {output : Output} (written : fromIpc ipc csv input = .ok output) :
    ∃ (source : Arrow.MixedFlat.Timestamp.Stream) (rows : Csv.Typed.Table (schemaOf source.fields) Cell),
      Arrow.MixedFlat.Timestamp.read ipc input = .ok source ∧ output.fields = source.fields ∧
      flatten source.fields source.batches = .ok rows ∧
      decode csv (schemaOf source.fields) output.wire = .ok rows := by
  cases decoded : Arrow.MixedFlat.Timestamp.read ipc input with
  | error cause => simp [fromIpc, decoded, Bind.bind, Except.bind, Except.mapError] at written
  | ok source =>
    simp only [fromIpc, decoded, Bind.bind, Except.bind, Except.mapError] at written
    obtain ⟨rows, fields, flattened, csvRead⟩ := fromStream_roundtrip written
    exact ⟨source, rows, rfl, fields, flattened, csvRead⟩

theorem ipc_roundtrip {sourceLimits outputLimits : Arrow.ObservationLimits} {csv : Limits}
    {input output : KBytes} {interchange : Output}
    (exported : fromIpc sourceLimits csv input = .ok interchange)
    (imported : toIpc csv outputLimits interchange.fields interchange.wire = .ok output) :
    ∃ source target : Arrow.MixedFlat.Timestamp.Stream,
      Arrow.MixedFlat.Timestamp.read sourceLimits input = .ok source ∧
      Arrow.MixedFlat.Timestamp.read outputLimits output = .ok target ∧
      RowEquivalent source target := by
  obtain ⟨source, rows, sourceRead, fields, flattened, csvRead⟩ := fromIpc_roundtrip exported
  rw [fields] at imported
  obtain ⟨restored, decoded, outputRead, targetRows⟩ := toIpc_readback imported
  have same := Except.ok.inj (csvRead.symm.trans decoded)
  subst restored
  exact ⟨source, _, sourceRead, outputRead, rfl, rows, flattened, targetRows⟩

theorem namedExport_roundtrip {Name : Type*} {db : NamedTable.Database Name} {name : Name}
    {fields : List Field} {limits : Limits} {output : Output}
    (written : NamedTable.exportCsv db name fields limits = .ok output) :
    ∃ (rows : Csv.Typed.Table (schemaOf fields) Cell),
      Silmaril.Relational.Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      output.fields = fields ∧ decode limits (schemaOf fields) output.wire = .ok rows := by
  open Silmaril.Relational Silmaril.Formats.Relational.NamedTable in
  cases found : Scan.observePacked db name with
  | none => simp [NamedTable.exportCsv, found] at written
  | some table =>
    obtain ⟨schema, rows⟩ := table
    cases matched : schemaMatches (schemaOf fields) schema with
    | false => simp [NamedTable.exportCsv, found, matched] at written
    | true =>
      have same := (schemaMatches_eq_true_iff _ _).mp matched
      subst schema
      cases encoded : encode limits (schemaOf fields) rows with
      | error cause =>
        simp [NamedTable.exportCsv, found, matched, encoded, Except.map, Except.mapError] at written
      | ok wire =>
        simp [NamedTable.exportCsv, found, matched, encoded, Except.map, Except.mapError] at written
        subst output
        exact ⟨rows, rfl, rfl, decode_encode encoded⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp
