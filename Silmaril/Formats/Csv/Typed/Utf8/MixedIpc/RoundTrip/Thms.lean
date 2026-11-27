module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Thms
public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Thms
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip.Correctness

public section

namespace Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip

open Silmaril.Relational
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

/-- The two successful public conversions keep the original descriptor
and exact ordered Scan table. The output has one complete batch through
exact EOS. Source, export, import, and writer limits apply independently. -/
theorem readback {source sink : Arrow.MixedFlat.Limits} {exportLimits importLimits : Limits}
    {input output : KBytes} {csv : Output}
    (exported : convert source exportLimits input = .ok csv)
    (emitted : ToIpc.convert importLimits sink csv.schema csv.wire = .ok output) :
    ∃ table, Rows.readRows source input = some table ∧ csv.schema = table.schema ∧
      Rows.readRows sink output = some table ∧
      readEvents sink output = some
        ⟨ToIpc.fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ :=
  Proofs.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip.readback exported emitted

/-- The round trip preserves row equivalence, which forgets the original batch partition. -/
theorem equivalent {source sink : Arrow.MixedFlat.Limits} {exportLimits importLimits : Limits}
    {input output : KBytes} {csv : Output}
    (exported : convert source exportLimits input = .ok csv)
    (emitted : ToIpc.convert importLimits sink csv.schema csv.wire = .ok output) :
    Rows.Equivalent source input sink output := by
  obtain ⟨table, fromSource, _, fromSink, _⟩ := readback exported emitted
  exact ⟨table, fromSource, fromSink⟩

end Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip
