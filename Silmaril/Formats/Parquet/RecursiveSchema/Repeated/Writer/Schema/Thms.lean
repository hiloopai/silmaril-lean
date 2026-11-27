module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema

@[expose] public section

theorem equal_exact {depth : Nat} {left right : Arrow.RecursiveSchema.Schema}
    (checked : equal depth left right = true) : left = right :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.equal_exact checked

/-- The exact inverse uses the original compiler on the emitted schema-only carrier. -/
theorem emit_wire {limits : Limits} {schema : Arrow.RecursiveSchema.Schema}
    {output : Checked limits} (written : emit limits schema = .ok output) : Wire limits schema output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.emit_wire written

theorem wrap_bytes {limits : Limits} {payload : Bytes} {plan : Plan}
    {groups : List GroupIndex} {out : Envelope} (built : wrap limits payload plan groups = .ok out) :
    ∃ footer, out.footer = ⟨4 + payload.length, 4 + payload.length + footer.length⟩ ∧
      out.bytes = (((Footer.magic.append payload).append footer).append
        (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.wrap_bytes built

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema
