module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs
import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc

open Silmaril.Formats Silmaril.Formats.Csv.Typed.Utf8.MixedIpc
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

theorem codecs_parsePrint (field : Arrow.MixedFlat.Field) : (codecs field).ParsePrint := by
  intro value text printed
  obtain ⟨name, nullable, kind⟩ := field
  cases kind with
  | primitive kind =>
    cases kind <;> cases value
    all_goals simp [codecs] at printed
    all_goals rename_i primitive
    all_goals cases primitive <;> simp at printed
    · simp [codecs, Csv.Typed.Codecs.int32_parsePrint printed]
    · simp [codecs, Csv.Typed.Utf8.string_parsePrint printed]
  | view kind =>
    cases kind <;> cases value <;> simp [codecs] at printed
    simp [codecs, Csv.Typed.Utf8.string_parsePrint printed]

theorem readScan_ok_iff {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {table : Rows.Table} :
    readScan limits wire = .ok table ↔ Rows.readRows limits wire = some table := by
  unfold readScan Rows.readRows readEvents
  generalize Arrow.MixedFlat.Stream.Events.readAll limits wire = events
  cases result : (complete events).bind Rows.toTable with
  | some observed => simp [result]
  | none =>
    cases events with
    | error cause => simp [result]
    | ok opened => cases terminal : opened.2.termination <;> simp [result, terminal]

theorem decode_encode {limits : Limits} {table : Rows.Table} {wire : Csv.Bytes}
    (written : encode limits table = .ok wire) :
    decode limits table.schema wire = .ok table := by
  cases schemaOk : checkSchema table.schema with
  | error cause => simp [encode, schemaOk, Bind.bind, Except.bind] at written
  | ok accepted =>
    cases accepted
    by_cases overRows : limits.maxRows < table.rows.length
    · simp [encode, schemaOk, overRows, Bind.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at written
    cases required : checkRequired table.schema table.rows with
    | error cause => simp [encode, schemaOk, overRows, required, Bind.bind, Except.bind] at written
    | ok accepted =>
      cases accepted
      cases encoded : Csv.Typed.Utf8.encode (csvSchema table.schema) codecs table.rows with
      | error cause =>
        simp [encode, schemaOk, overRows, required, encoded, Except.mapError, Bind.bind, Except.bind] at written
      | ok output =>
        by_cases overBytes : limits.maxBytes < output.length
        · simp [encode, schemaOk, overRows, required, encoded, overBytes, Except.mapError, Bind.bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw] at written
        have same : output = wire := by
          simpa [encode, schemaOk, overRows, required, encoded, overBytes, Except.mapError, Bind.bind,
            Except.bind, pure, Except.pure] using written
        subst wire
        have lexical := Csv.Typed.Utf8.decode_encode codecs_parsePrint encoded
        have bounded := (Csv.Typed.Utf8.Bounded.decode_ok_iff (csvSchema table.schema) codecs
          limits.maxRows output table.rows).mpr ⟨lexical, Nat.le_of_not_gt overRows⟩
        simp [decode, overBytes, schemaOk, bounded, required, Except.mapError, Bind.bind, Except.bind,
          pure, Except.pure]

theorem convert_roundtrip {ipc : Arrow.MixedFlat.Limits} {csv : Limits} {input : KBytes} {output : Output}
    (written : convert ipc csv input = .ok output) :
    ∃ table, Rows.readRows ipc input = some table ∧ output.schema = table.schema ∧
      decode csv output.schema output.wire = .ok table := by
  cases read : readScan ipc input with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok table =>
    cases encoded : encode csv table with
    | error cause => simp [convert, read, encoded, Except.mapError, Bind.bind, Except.bind] at written
    | ok wire =>
      have same : (⟨table.schema, wire⟩ : Output) = output := by
        simpa [convert, read, encoded, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] using written
      subst output
      exact ⟨table, readScan_ok_iff.mp read, rfl, decode_encode encoded⟩

private theorem decode_rows {limits : Limits} {schema : Rows.Schema} {wire : Csv.Bytes} {table : Rows.Table}
    (read : decode limits schema wire = .ok table) :
    ∃ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
      table = ⟨schema, rows⟩ := by
  by_cases over : limits.maxBytes < wire.length
  · simp [decode, over, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at read
  cases profile : checkSchema schema with
  | error cause => simp [decode, over, profile, Bind.bind, Except.bind] at read
  | ok checked =>
    cases checked
    cases parsed : Csv.Typed.Utf8.Bounded.decode limits.maxRows (csvSchema schema) codecs wire with
    | error cause =>
      cases cause <;>
        simp [decode, over, profile, parsed, Except.mapError, Bind.bind, Except.bind] at read
    | ok rows =>
      cases required : checkRequired schema rows with
      | error cause =>
        simp [decode, over, profile, parsed, required, Except.mapError, Bind.bind, Except.bind] at read
      | ok checked =>
        cases checked
        have exact : (⟨schema, rows⟩ : Rows.Table) = table := by
          simpa [decode, over, profile, parsed, required, Except.mapError, Bind.bind, Except.bind,
            pure, Except.pure] using read
        exact ⟨rows, ((Csv.Typed.Utf8.Bounded.decode_ok_iff _ _ _ _ _).mp parsed).1, exact.symm⟩

theorem decode_agrees {leftLimits rightLimits : Limits} {schema : Rows.Schema} {wire : Csv.Bytes}
    {left right : Rows.Table}
    (leftRead : decode leftLimits schema wire = .ok left)
    (rightRead : decode rightLimits schema wire = .ok right) :
    left = right := by
  obtain ⟨leftRows, leftRaw, leftTable⟩ := decode_rows leftRead
  obtain ⟨rightRows, rightRaw, rightTable⟩ := decode_rows rightRead
  have same := Except.ok.inj (leftRaw.symm.trans rightRaw)
  rw [leftTable, rightTable, same]

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc
