module

public import Silmaril.Formats.Arrow.DateUtf8Stream.Defs

public section

namespace Silmaril.Proofs.Formats.Arrow.DateUtf8Stream

open Silmaril.Formats.Arrow.DateUtf8Stream

theorem emit_readback {limits : Silmaril.Formats.Arrow.ObservationLimits} {schema : Schema}
    {batches : List Batch} {wire : KBytes} (written : emit limits schema batches = .ok wire) :
    read limits wire = .ok ⟨schema, batches⟩ := by
  unfold emit at written
  cases serialized : serialize limits schema batches with
  | error cause => simp [serialized, Bind.bind, Except.bind] at written
  | ok bytes =>
    cases decoded : read limits bytes with
    | error cause => simp [serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok observed =>
      by_cases same : observed = ⟨schema, batches⟩
      · have equal : bytes = wire := by
          simpa [serialized, decoded, same, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] using written
        simpa [equal, same] using decoded
      · simp [serialized, decoded, same, Bind.bind, Except.bind, Except.mapError] at written

end Silmaril.Proofs.Formats.Arrow.DateUtf8Stream
