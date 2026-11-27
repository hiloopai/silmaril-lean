module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.ToIpc

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Compiled)
open Silmaril.Formats.Parquet.RecursiveSchema.Rows (Limits GroupWire readAll readAll_wire)
open Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer (emit emit_readback Readback)

theorem convert_readback {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Limits} {ipc : Formats.Arrow.RecursiveSchema.Batch.Limits}
    {schema : Compiled schemaLimits snapshot} {bytes : KBytes}
    (written : convert limits ipc schema = .ok bytes) :
    ∃ groups, readAll limits schema = .ok groups ∧
      List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) groups ∧
      Readback ipc schema.arrow groups bytes := by
  cases source : readAll limits schema with
  | error cause => simp [convert, source, Except.mapError, bind, Except.bind] at written
  | ok groups =>
    cases emitted : emit ipc schema.arrow groups with
    | error cause => simp [convert, source, emitted, Except.mapError, bind, Except.bind] at written
    | ok wire =>
      simp only [convert, source, emitted, Except.mapError, bind, Except.bind, Except.ok.injEq] at written
      exact ⟨groups, rfl, readAll_wire source, written ▸ emit_readback emitted⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.ToIpc
