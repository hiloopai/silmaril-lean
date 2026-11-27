module

public import Silmaril.Formats.Csv.Typed.Utf8.MixedTimestamp.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.WithTimestamp.Thms
import Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp.Correctness

public section

namespace Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp

open Silmaril.Formats
open Csv.Typed.Utf8.MixedTimestamp
open Arrow.MixedFlat.Timestamp (Stream)
open Parquet.MixedV1Writer.FromIpc.WithTimestamp (Limits convert convert_readback ordinals)

theorem ipc_parquet_roundtrip
    {sourceLimits outputLimits : Arrow.ObservationLimits} {csv : Csv.Typed.Utf8.MixedTimestamp.Limits}
    {parquet : Parquet.MixedV1Writer.FromIpc.WithTimestamp.Limits} {input output : KBytes} {wire : Bytes} {interchange : Output}
    (exported : fromIpc sourceLimits csv input = .ok interchange)
    (imported : toIpc csv outputLimits interchange.fields interchange.wire = .ok output)
    (written : convert outputLimits parquet output = .ok wire) :
    ∃ (source : Stream) (projected : Parquet.FlatProjection.Events.Checked),
      Arrow.MixedFlat.Timestamp.read sourceLimits input = .ok source ∧
      Parquet.FlatProjection.Events.readAll parquet.readback wire (ordinals source) =
        .ok ⟨projected.schema, projected.trace parquet.readback⟩ ∧
      (projected.trace parquet.readback).termination = .eos ∧
      RowEquivalent source (Parquet.FlatProjection.Events.ToIpc.observation (projected.trace parquet.readback)) := by
  obtain ⟨source, target, sourceRead, targetRead, equivalent⟩ := ipc_roundtrip exported imported
  obtain ⟨restored, projected, _, restoredRead, _, _, _, projectedRead, eos, observed⟩ := convert_readback written
  have same := Except.ok.inj (restoredRead.symm.trans targetRead)
  rw [same] at projectedRead observed
  have order : ordinals source = ordinals target := congrArg
    (fun fields : List Field => Array.range fields.length) equivalent.choose
  exact ⟨source, projected, sourceRead, order ▸ projectedRead, eos, observed ▸ equivalent⟩

end Silmaril.Proofs.Formats.Csv.Typed.Utf8.MixedTimestamp
