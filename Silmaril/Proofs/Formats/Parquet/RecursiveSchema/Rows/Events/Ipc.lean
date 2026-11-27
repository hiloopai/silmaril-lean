module

public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events.Prefix
import Silmaril.Formats.Parquet.RecursiveSchema.Rows.ToIpc.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.RecursiveSchema
open Silmaril.Formats.Parquet.RecursiveSchema.Rows.Events
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
  have checked := (Arrow.RecursiveSchema.Stream.read_iff.mp strict).1
  obtain ⟨original, nativeChecked, _, nativeFields, nativeBatches, nativeEnd⟩ :=
    (Arrow.RecursiveSchema.Stream.Events.read_wire readback).trace
  rw [checked] at nativeChecked
  cases Except.ok.inj nativeChecked
  have wire := readSource_wire accepted
  obtain ⟨sameGroups, directEnd⟩ := prefix_of_all wire.groups all
  exact ⟨by rw [wire.fields, nativeFields, fields],
    sameGroups.trans (nativeBatches.trans batches).symm,
    directEnd, by rw [nativeEnd, eos]; rfl⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Rows.Events
