module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.Defs
public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Events.Thms
import Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.Agreement

public section

namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events

open Silmaril.Relational
open MixedFlat.LargeUtf8.Events

/-- The pull drain agrees with the direct read at every completed batch and
at the terminal outcome, including the first original record failure. -/
theorem readAll_exact (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes) :
    match Stream.read limits framing input with
    | .error cause => readAll limits framing input = .error (.schema cause)
    | .ok direct =>
      ∃ trace : Trace (schema direct.fields),
        readAll limits framing input = .ok ⟨schema direct.fields, trace⟩ ∧
        trace.termination = observeTermination direct.trace.termination ∧
        List.Forall₂ (fun record event => Agrees (schema direct.fields) record.observed event)
          direct.trace.batches trace.batches :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.readAll_exact limits framing input

/-- Project each direct batch at the same typed schema positions while
retaining the complete batch prefix and original terminal outcome. -/
theorem readProjected_exact (limits : MixedFlat.Limits) (framing : Framing) (input : KBytes)
    (projection : (source : Signature) → Scan.Projection source) :
    match Stream.read limits framing input with
    | .error cause => readProjected limits framing input projection = .error (.schema cause)
    | .ok direct =>
      let selection := projection (schema direct.fields)
      ∃ trace : Trace selection.schema,
        readProjected limits framing input projection = .ok ⟨selection.schema, trace⟩ ∧
        trace.termination = observeTermination direct.trace.termination ∧
        List.Forall₂ (fun record event => Projects selection record.observed event)
          direct.trace.batches trace.batches :=
  Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events.readProjected_exact limits framing input projection

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Events
