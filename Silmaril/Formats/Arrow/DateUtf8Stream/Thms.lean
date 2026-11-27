module

public import Silmaril.Formats.Arrow.DateUtf8Stream.Defs
import Silmaril.Proofs.Formats.Arrow.DateUtf8Stream.Readback

public section

namespace Silmaril.Formats.Arrow.DateUtf8Stream

/-- Successful emission recovers the typed field order and every batch through exact EOS. -/
theorem emit_readback {limits : ObservationLimits} {schema : Schema} {batches : List Batch} {wire : KBytes}
    (written : emit limits schema batches = .ok wire) :
    read limits wire = .ok ⟨schema, batches⟩ :=
  Proofs.Formats.Arrow.DateUtf8Stream.emit_readback written

end Silmaril.Formats.Arrow.DateUtf8Stream
