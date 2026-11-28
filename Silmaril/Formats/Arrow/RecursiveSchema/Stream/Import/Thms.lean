module

public import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Stream.Import.Admission

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import

public section

theorem admit_iff {limits : Batch.Limits} {input : KBytes} {source : Trace} :
    admit limits input = .ok source ↔ read limits input = .ok source :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Import.admit_iff

theorem admit_wire {limits : Batch.Limits} {input : KBytes} {source : Trace}
    (accepted : admit limits input = .ok source) : SourceWire limits input source :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Import.admit_wire accepted

theorem admit_terminal_wire {limits : Batch.Limits} {input : KBytes} {source : Trace}
    (rejected : admit limits input = .error (.terminal source)) : TerminalWire limits input source :=
  Proofs.Formats.Arrow.RecursiveSchema.Stream.Import.admit_terminal_wire rejected

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Import
