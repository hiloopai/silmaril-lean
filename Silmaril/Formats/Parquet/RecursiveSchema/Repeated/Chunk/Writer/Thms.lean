module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Page

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer

@[expose] public section

/-- Serialization preserves the original ordered level sections and signed suffix
and uses the measured size in both V1 size fields. -/
theorem serialize_construction {limits : Chunk.Limits} {input : Input} {output : Output}
    (written : serialize limits input = .ok output) : Construction limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.construction written

theorem agrees_exact {input : Input} {after : Chunk.State} {page : Chunk.DecodedPage}
    (checked : agrees input after page = true) :
    page.levels = input.atoms.map (·.levels) ∧
      page.words = input.atoms.map (·.word) ∧ page.after = after :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.agrees_exact checked

/-- The runtime certificate recovers the exact original atoms from the whole
emitted frame at the caller's state. -/
theorem certify_readback {limits : Chunk.Limits} {input : Input} {output : Output}
    (checked : certify limits input output = .ok ()) : Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.readback checked

/-- The final slot counts every atom. The final row count counts only
repetition-zero atoms, even when the page begins inside a List. -/
theorem Readback.state_counts {limits : Chunk.Limits} {input : Input} {output : Output}
    (accepted : Readback limits input output) :
    input.start.slot + input.atoms.length = output.after.slot ∧
      input.start.rows + (input.atoms.map (·.levels)).countP Chunk.LevelSlot.startsRow =
        output.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.state_counts accepted

/-- Successful native page emission has both the construction and strict
readback witnesses. -/
theorem emit_wire {limits : Chunk.Limits} {input : Input} {output : Output}
    (written : emit limits input = .ok output) :
    Construction limits input output ∧ Readback limits input output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.emit_wire written

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer
