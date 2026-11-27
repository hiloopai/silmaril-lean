module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events.Prefix
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RecursiveSchema.Repeated
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events
open Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)

public theorem agrees_ipc {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Rows.Limits} {schema : Compiled schemaLimits snapshot}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {bytes : KBytes}
    {direct : Σ source : Signature, Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (accepted : readSource limits schema = .ok direct)
    (written : Rows.ToIpc.convert limits ipc schema = .ok bytes)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc bytes = .ok native) :
    declarations direct.1 = declarations native.1 ∧
      direct.2.batches.map eraseBatch = native.2.batches.map eraseBatch ∧
      direct.2.termination = .eos ∧ native.2.termination = .eos := by
  obtain ⟨groups, all, _, certificate⟩ := Rows.ToIpc.convert_readback written
  obtain ⟨trace, offset, strict, _, fields, batches, eos, _, _⟩ := certificate.result
  obtain ⟨nativeFields, nativeBatches, nativeEnd⟩ :=
    Arrow.RecursiveSchema.Stream.Events.read_checked_eos strict eos readback
  have wire := readSource_wire accepted
  obtain ⟨sameGroups, directEnd⟩ := prefix_of_all wire.groups all
  exact ⟨by rw [wire.fields, nativeFields, fields],
    sameGroups.trans (nativeBatches.trans batches).symm,
    directEnd, nativeEnd⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Rows.Events
