module

public import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Arrow.Binary.StreamWriter.Thms
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Hex.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Bounded.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc

open Silmaril.Formats
open Silmaril.Formats.Csv.Typed hiding encode decode
open Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

private theorem mapError_ok {α ε η : Type} {result : Except ε α} {adapt : ε → η}
    {value : α} (ok : result.mapError adapt = .ok value) : result = .ok value := by
  cases result with
  | error cause => simp [Except.mapError] at ok
  | ok actual =>
    change (.ok actual : Except η α) = .ok value at ok
    exact congrArg Except.ok (Except.ok.inj ok)

theorem emitIpc_readback {limits : IpcLimits} {field : Descriptor} {values : Slots} {wire : KBytes}
    (written : emitIpc limits field values = .ok wire) :
    readIpc limits field.layout wire = .ok ⟨field, [values]⟩ := by
  let packed := values.map (Option.map (fun bytes => Arrow.Writer.emitWords 1 (bytes.map UInt8.toNat)))
  have normalized : packed.map (Option.map KBytes.toList) = values := by
    simp [packed, List.map_map, Option.map_map, Function.comp_def, Arrow.Writer.emitBytes_bytes]
  rcases field with ⟨name, nullable, layout⟩
  cases layout
  · have emitted : Arrow.BinaryView.StreamWriter.emit limits.ipc limits.view
        ⟨name, nullable, .binary⟩ [packed] = .ok wire := mapError_ok written
    obtain ⟨decoded, read, rows⟩ := Arrow.BinaryView.StreamWriter.emit_binary_readback emitted
    have exactRows : decoded.map (Arrow.BinaryView.StreamWriter.observe .binary) = [values] := by
      change decoded.map (List.map (Option.map KBytes.toList)) = _
      rw [rows]
      exact congrArg (fun slots => [slots]) normalized
    simp [readIpc, read, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]
    exact exactRows
  · have emitted : Arrow.Binary.StreamWriter.emit limits.ipc ⟨name, nullable⟩ [packed] = .ok wire :=
      mapError_ok written
    obtain ⟨decoded, read, ⟨descriptor, rows⟩, _⟩ := Arrow.Binary.StreamWriter.emit_readback emitted
    have exactRows : decoded.batches.map (Arrow.Binary.StreamWriter.observe ∘ Arrow.Binary.Stream.Batch.values) =
        [values] := by
      rw [rows]
      exact congrArg (fun slots => [slots]) normalized
    simp [readIpc, read, descriptor, exactRows, Except.mapError, Bind.bind, Except.bind, pure, Except.pure]

private theorem decode_spec {limits : CsvLimits} {field : Descriptor} {wire : Csv.Bytes} {values : Slots} :
    decode limits field wire = .ok values ↔ wire.length ≤ limits.maxBytes ∧
      ∃ rows, Utf8.decode (schema field) codecs wire = .ok rows ∧ rows.length ≤ limits.maxRows ∧
        values = readRows rows ∧ checkRequired field values = .ok () := by
  constructor
  · intro parsed
    by_cases tooWide : limits.maxBytes < wire.length
    · simp [decode, tooWide, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at parsed
    cases bounded : Utf8.Bounded.decode limits.maxRows (schema field) codecs wire with
    | error cause =>
      cases cause <;> simp [decode, tooWide, bounded, Except.mapError, Bind.bind, Except.bind] at parsed
    | ok rows =>
      cases required : checkRequired field (readRows rows) with
      | error cause =>
        simp [decode, tooWide, bounded, required, Except.mapError, Bind.bind, Except.bind] at parsed
      | ok checked =>
        cases checked
        have same : readRows rows = values := by
          simpa [decode, tooWide, bounded, required, Except.mapError, Bind.bind, Except.bind, pure,
            Except.pure] using parsed
        obtain ⟨raw, count⟩ := (Utf8.Bounded.decode_ok_iff _ _ _ _ _).mp bounded
        exact ⟨Nat.le_of_not_gt tooWide, rows, raw, count, same.symm, by simpa [same] using required⟩
  · rintro ⟨byteBound, rows, raw, rowBound, rfl, required⟩
    have bounded := (Utf8.Bounded.decode_ok_iff _ _ _ _ _).mpr ⟨raw, rowBound⟩
    simp [decode, Nat.not_lt_of_ge byteBound, bounded, required, Except.mapError, Bind.bind, Except.bind,
      pure, Except.pure]

private theorem decode_agrees {left right : CsvLimits} {field : Descriptor} {wire : Csv.Bytes}
    {a b : Slots} (readLeft : decode left field wire = .ok a) (readRight : decode right field wire = .ok b) :
    a = b := by
  obtain ⟨_, xs, leftRaw, _, rfl, _⟩ := decode_spec.mp readLeft
  obtain ⟨_, ys, rightRaw, _, rfl, _⟩ := decode_spec.mp readRight
  rw [Except.ok.inj (leftRaw.symm.trans rightRaw)]

theorem decode_encode {limits : CsvLimits} {field : Descriptor} {values : Slots} {wire : Csv.Bytes}
    (written : encode limits field values = .ok wire) : decode limits field wire = .ok values := by
  by_cases tooMany : limits.maxRows < values.length
  · simp [encode, tooMany, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at written
  cases required : checkRequired field values with
  | error cause => simp [encode, tooMany, required, Bind.bind, Except.bind] at written
  | ok checked =>
    cases checked
    cases raw : Utf8.encode (schema field) codecs (values.map fun cell _ => cell) with
    | error cause => simp [encode, tooMany, required, raw, Except.mapError, Bind.bind, Except.bind] at written
    | ok bytes =>
      by_cases tooWide : limits.maxBytes < bytes.length
      · simp [encode, tooMany, required, raw, tooWide, Except.mapError, Bind.bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at written
      have exactWire : bytes = wire := by
        simpa [encode, tooMany, required, raw, tooWide, Except.mapError, Bind.bind, Except.bind,
          pure, Except.pure] using written
      subst wire
      have parsed := Utf8.decode_encode (fun _ => Codecs.Hex.parsePrint) raw
      exact decode_spec.mpr ⟨Nat.le_of_not_gt tooWide, _, parsed, by simpa using Nat.le_of_not_gt tooMany,
        by simp [readRows, List.map_map, Function.comp_def], required⟩

theorem toCsv_observation {ipc : IpcLimits} {csv : CsvLimits} {layout : Layout} {input : KBytes}
    {output : Output} (converted : toCsv ipc csv layout input = .ok output) :
    ∃ observed, readIpc ipc layout input = .ok observed ∧ output.field = observed.field ∧
      encode csv observed.field observed.batches.flatten = .ok output.wire := by
  cases read : readIpc ipc layout input with
  | error cause => simp [toCsv, read, Except.mapError, Bind.bind, Except.bind] at converted
  | ok observed =>
    cases encoded : encode csv observed.field observed.batches.flatten with
    | error cause => simp [toCsv, read, encoded, Except.mapError, Bind.bind, Except.bind] at converted
    | ok wire =>
      have same : (⟨observed.field, wire⟩ : Output) = output := by
        simpa [toCsv, read, encoded, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] using converted
      subst output
      exact ⟨observed, rfl, rfl, encoded⟩

theorem fromCsv_readback {ipc : IpcLimits} {csv : CsvLimits} {field : Descriptor} {input : Csv.Bytes}
    {output : KBytes} (converted : fromCsv csv ipc field input = .ok output) :
    ∃ values, decode csv field input = .ok values ∧ readIpc ipc field.layout output = .ok ⟨field, [values]⟩ := by
  cases parsed : decode csv field input with
  | error cause => simp [fromCsv, parsed, Except.mapError, Bind.bind, Except.bind] at converted
  | ok values =>
    have written : emitIpc ipc field values = .ok output := mapError_ok (by
      simpa [fromCsv, parsed, Except.mapError, Bind.bind, Except.bind] using converted)
    exact ⟨values, rfl, emitIpc_readback written⟩

theorem roundtrip {source sink : IpcLimits} {exportLimits importLimits : CsvLimits} {layout : Layout}
    {input output : KBytes} {csv : Output} (exported : toCsv source exportLimits layout input = .ok csv)
    (emitted : fromCsv importLimits sink csv.field csv.wire = .ok output) :
    ∃ original, readIpc source layout input = .ok original ∧ csv.field = original.field ∧
      readIpc sink original.field.layout output = .ok ⟨original.field, [original.batches.flatten]⟩ := by
  obtain ⟨original, read, field, encoded⟩ := toCsv_observation exported
  obtain ⟨values, decoded, outputRead⟩ := fromCsv_readback emitted
  rw [field] at decoded outputRead
  have same := decode_agrees decoded (decode_encode encoded)
  subst values
  exact ⟨original, read, field, outputRead⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc
