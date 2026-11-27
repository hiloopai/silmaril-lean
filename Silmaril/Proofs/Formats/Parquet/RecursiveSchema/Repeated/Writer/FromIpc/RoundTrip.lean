module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.ToIpc.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc.Conversion

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc

open Silmaril.Formats
open Parquet.RecursiveSchema.Repeated
open Parquet.RecursiveSchema.Repeated.Writer.FromIpc
open Arrow.RecursiveSchema.Stream (Completed)

public theorem round_trip {limits : Limits} {options : Options} {input returned : KBytes}
    {output : Writer.Output} {ipc : Arrow.RecursiveSchema.Batch.Limits}
    {decoded : Source limits.parquet.schema.snapshot output.bytes}
    (written : convert limits options input = .ok output)
    (opened : openFile limits.parquet.schema.snapshot output.bytes = .ok decoded)
    (reverse : Rows.ToIpc.convert limits.parquet.rows ipc decoded.schema = .ok returned) :
    RoundTripWire limits.ipc ipc input returned := by
  obtain ⟨original, fileSource, source, reopened, _, _, _, schema, _, observed, _⟩ :=
    file (convert_readback written)
  have sameFile := Except.ok.inj (reopened.symm.trans opened)
  subst fileSource
  obtain ⟨groups, read, _, emitted⟩ := Rows.ToIpc.convert_readback reverse
  have sameGroups := Except.ok.inj (read.symm.trans observed)
  subst groups
  obtain ⟨result, offset, strict, wire, fields, batches, terminal, eos, endAt⟩ := emitted.result
  exact ⟨original, result, offset, source, strict, wire, fields.trans schema,
    batches, by simpa only [List.length_map] using terminal, eos, endAt⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.FromIpc
