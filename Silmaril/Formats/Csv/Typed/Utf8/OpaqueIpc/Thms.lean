module

public import Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc

/-- The bounded typed CSV decoder recovers every original nullable octet row. -/
theorem decode_encode {limits : CsvLimits} {field : Descriptor} {values : Slots} {wire : Csv.Bytes}
    (written : encode limits field values = .ok wire) : decode limits field wire = .ok values :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.decode_encode written

/-- Successful imports of the same declared descriptor and wire agree
under independent byte and row limits. -/
theorem decode_agrees {left right : CsvLimits} {field : Descriptor} {wire : Csv.Bytes} {a b : Slots}
    (readLeft : decode left field wire = .ok a) (readRight : decode right field wire = .ok b) : a = b :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.decode_agrees readLeft readRight

/-- A successful export comes from a complete checked source with this exact
descriptor and the original ordered rows flattened across batches. -/
theorem toCsv_observation {ipc : IpcLimits} {csv : CsvLimits} {layout : Layout} {input : KBytes}
    {output : Output} (converted : toCsv ipc csv layout input = .ok output) :
    ∃ observed, readIpc ipc layout input = .ok observed ∧ output.field = observed.field ∧
      encode csv observed.field observed.batches.flatten = .ok output.wire :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.toCsv_observation converted

theorem emitIpc_readback {limits : IpcLimits} {field : Descriptor} {values : Slots} {wire : KBytes}
    (written : emitIpc limits field values = .ok wire) :
    readIpc limits field.layout wire = .ok ⟨field, [values]⟩ :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.emitIpc_readback written

/-- Successful CSV import emits the exact declared field and ordered octets
in one batch, checked through EOS. -/
theorem fromCsv_readback {ipc : IpcLimits} {csv : CsvLimits} {field : Descriptor} {input : Csv.Bytes}
    {output : KBytes} (converted : fromCsv csv ipc field input = .ok output) :
    ∃ values, decode csv field input = .ok values ∧ readIpc ipc field.layout output = .ok ⟨field, [values]⟩ :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.fromCsv_readback converted

/-- Either opaque layout preserves its exact descriptor and flattened rows
through the two checked public calls under independent limits. -/
theorem roundtrip {source sink : IpcLimits} {exportLimits importLimits : CsvLimits} {layout : Layout}
    {input output : KBytes} {csv : Output} (exported : toCsv source exportLimits layout input = .ok csv)
    (emitted : fromCsv importLimits sink csv.field csv.wire = .ok output) :
    ∃ original, readIpc source layout input = .ok original ∧ csv.field = original.field ∧
      readIpc sink original.field.layout output = .ok ⟨original.field, [original.batches.flatten]⟩ :=
  Proofs.Formats.Csv.Typed.Utf8.OpaqueIpc.roundtrip exported emitted

end Silmaril.Formats.Csv.Typed.Utf8.OpaqueIpc
