module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Defs
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc

open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

/-- Each supported present value round-trips in its declared Arrow kind. -/
theorem codecs_parsePrint (field : Arrow.MixedFlat.Field) : (codecs field).ParsePrint :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.codecs_parsePrint field

/-- The typed Scan handoff observes exactly the existing complete IPC table. -/
theorem readScan_ok_iff {limits : Arrow.MixedFlat.Limits} {wire : KBytes} {table : Rows.Table} :
    readScan limits wire = .ok table ↔ Rows.readRows limits wire = some table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.readScan_ok_iff

/-- Checked re-import with the same limits and out-of-band descriptor
recovers the exact dependent table, including rows at width zero. -/
theorem decode_encode {limits : Limits} {table : Rows.Table} {wire : Csv.Bytes}
    (written : encode limits table = .ok wire) :
    decode limits table.schema wire = .ok table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.decode_encode written

/-- Successful checked imports of the same descriptor and bytes agree
under independent byte and row caps. -/
theorem decode_agrees {leftLimits rightLimits : Limits} {schema : Rows.Schema} {wire : Csv.Bytes}
    {left right : Rows.Table}
    (leftRead : decode leftLimits schema wire = .ok left)
    (rightRead : decode rightLimits schema wire = .ok right) :
    left = right :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.decode_agrees leftRead rightRead

/-- A successful decode retains the declared ordered descriptor. -/
theorem decode_schema {limits : Limits} {schema : Rows.Schema} {wire : Csv.Bytes} {table : Rows.Table}
    (read : decode limits schema wire = .ok table) : table.schema = schema :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.decode_schema read

/-- IPC → Scan → typed CSV → Scan commutes on every successful conversion.
The result retains the original ordered Arrow descriptor and flattened rows. -/
theorem convert_roundtrip {ipc : Arrow.MixedFlat.Limits} {csv : Limits} {input : KBytes} {output : Output}
    (written : convert ipc csv input = .ok output) :
    ∃ table, Rows.readRows ipc input = some table ∧ output.schema = table.schema ∧
      decode csv output.schema output.wire = .ok table :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.convert_roundtrip written

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc
