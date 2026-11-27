module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.Thms
public import Silmaril.Formats.Csv.Typed.Utf8.MixedIpc.ToIpc.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip

open Silmaril.Formats Silmaril.Relational
open Silmaril.Formats.Csv.Typed.Utf8.MixedIpc
open Silmaril.Formats.Parquet.FlatProjection.Composition.Ipc

theorem readback {source sink : Arrow.MixedFlat.Limits} {exportLimits importLimits : Limits}
    {input output : KBytes} {csv : Output}
    (exported : convert source exportLimits input = .ok csv)
    (emitted : ToIpc.convert importLimits sink csv.schema csv.wire = .ok output) :
    ∃ table, Rows.readRows source input = some table ∧ csv.schema = table.schema ∧
      Rows.readRows sink output = some table ∧
      readEvents sink output = some
        ⟨ToIpc.fields table.schema, [Rows.observeColumns (AlignedColumns.ofRows table.rows)]⟩ := by
  obtain ⟨original, sourceRead, descriptor, exportRead⟩ := convert_roundtrip exported
  obtain ⟨recovered, importRead, _, events, sinkRead⟩ := ToIpc.convert_readback emitted
  have sameTable := decode_agrees exportRead importRead
  subst recovered
  exact ⟨original, sourceRead, descriptor, sinkRead, by simpa [descriptor] using events⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedIpc.RoundTrip
