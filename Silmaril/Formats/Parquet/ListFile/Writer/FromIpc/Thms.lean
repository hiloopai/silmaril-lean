module

public import Silmaril.Formats.Parquet.ListFile.Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.ListFile.Multi.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.ListFile.Writer.FromIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.ListFile.Writer.FromIpc

/-- A source failure retains the exact original error and has no Parquet carrier. -/
theorem convert_source_error {limits : Limits} {input : KBytes}
    {cause : Arrow.ListInt32.Stream.Error}
    (failed : Arrow.ListInt32.Stream.read limits.ipc input = .error cause) :
    convert limits input = .error (.source cause) :=
  Proofs.Formats.Parquet.ListFile.Writer.FromIpc.convert_source_error failed

/-- A complete source with a noncanonical child name is refused with that original name. -/
theorem convert_child_name {limits : Limits} {input : KBytes}
    {observed : Arrow.ListInt32.Stream.Observed}
    (decoded : Arrow.ListInt32.Stream.read limits.ipc input = .ok observed)
    (unsupported : observed.field.childName ≠ "element") :
    convert limits input = .error (.childName observed.field.childName) :=
  Proofs.Formats.Parquet.ListFile.Writer.FromIpc.convert_child_name decoded unsupported

/-- The successful source framing and footer-ordered Parquet readback describe the same nested rows. -/
theorem convert_readback {limits : Limits} {input : KBytes} {output : Writer.Encoded}
    (h : convert limits input = .ok output) : Readback limits input output :=
  Proofs.Formats.Parquet.ListFile.Writer.FromIpc.convert_readback h

/-- Two successful conversions preserve the Arrow field and every ordered batch observation. -/
theorem roundTrip {limits : Limits} {returned : Arrow.ListInt32.Stream.Limits}
    {input output : KBytes} {parquet : Writer.Encoded}
    (forward : convert limits input = .ok parquet)
    (backward : (Multi.ToIpc.convert ⟨limits.parquet.readback, returned⟩ parquet.bytes).wire = .ok output) :
    ∃ before after,
      Arrow.ListInt32.Stream.read limits.ipc input = .ok before ∧
      Arrow.ListInt32.Stream.read returned output = .ok after ∧
      observation before = observation after :=
  Proofs.Formats.Parquet.ListFile.Writer.FromIpc.roundTrip forward backward

end Silmaril.Formats.Parquet.ListFile.Writer.FromIpc
