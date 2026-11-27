module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted

public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted

/-- Once the original body, metadata bounds and running row/cell checks
have passed, every remaining parser rejection belongs to the sum. -/
theorem readParsed_covered {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {rowsBefore : Nat} {fault : MixedFlat.Error}
    (source : body.wf = true) (extent : metadata.bodyLength = body.len)
    (aligned : body.len % 8 = 0) (bodyCap : body.len ≤ limits.observation.ipc.bodyBytes)
    (fieldCap : fields.length ≤ limits.observation.ipc.fields)
    (rowCap : metadata.batch.rowCount ≤ limits.observation.ipc.rows)
    (budget : Body.checkBudget limits.observation fields.length (rowsBefore + metadata.batch.rowCount) = .ok ())
    (failed : MixedFlat.readParsed limits fields metadata body = .error fault) :
    ∃ cause : Cause, cause.batchError = .decode fault :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.readParsed_covered
    source extent aligned bodyCap fieldCap rowCap budget failed

/-- Recover the exact original rejected frame, prefix ranges and immutable causes. -/
theorem rejection_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : Agreement limits wire run :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.rejection_exact
    run

/-- The zero-based rejection ordinal equals the number of complete published batches. -/
theorem ordinal_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) : run.ordinal = run.batches.length :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.ordinal_exact
    run

/-- The immutable pull trace retains exactly the published prefix and terminal cause. -/
theorem pull_exact {limits : Incremental.Limits} {wire : KBytes}
    (run : Run limits wire) :
    Stream.Events.readAll limits.mixed (Portable.reference wire) =
      .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event,
        .readError run.nativeCause⟩⟩ :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.pull_exact
    run

/-- Admitted schedules on the same octets and limits give the same trace, ranges and cause. -/
theorem schedules_equivalent {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (a : Run limits left) (b : Run limits right) :
    a.ranges = b.ranges ∧ a.cause = b.cause ∧ a.trace = b.trace :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.schedules_equivalent
    leftWf rightWf octets a b

/-- A rejected carrier cannot finish successfully under the same limits. -/
theorem no_success {limits : Incremental.Limits} {left right : KBytes}
    (leftWf : left.wf = true) (rightWf : right.wf = true) (octets : left.toList = right.toList)
    (failed : Run limits left) (succeeded : Portable.Completed limits right) :
    False :=
  Proofs.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted.no_success
    leftWf rightWf octets failed succeeded

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Failure.Admitted
