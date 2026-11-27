module

public import Silmaril.Formats.Arrow.Framing.Incremental.Defs
import Silmaril.Proofs.Formats.Arrow.Framing.Incremental.Feed

public section

namespace Silmaril.Formats.Arrow.Framing.Incremental

/-- Each request retains exactly the wanted prefix and returns the untouched
suffix, independent of the rope shapes used for incoming bytes. -/
theorem buffer_feed {capacity : Nat} (buffer : Buffer capacity) (chunk : KBytes)
    (valid : chunk.wf = true) :
    let filled := buffer.feed chunk valid
    let bytes := buffer.bytes.toList ++ chunk.toList
    filled.buffered.bytes.toList = bytes.take capacity ∧
      filled.rest.toList = bytes.drop capacity ∧ filled.rest.wf = true :=
  Proofs.Formats.Arrow.Framing.Incremental.buffer_feed buffer chunk valid

/-- Start at an absolute offset in the immutable reference. -/
theorem start_refines {limits : Limits} {input : KBytes} {offset : Nat} (bounded : offset ≤ input.len) :
    (start offset).InCarrier limits input :=
  Proofs.Formats.Arrow.Framing.Incremental.start_refines bounded

/-- A successful feed preserves the immutable reference for the next ordered
chunk or returned suffix. Any emitted frame agrees with the carrier decoders. -/
theorem feed_refines {limits : Limits} {input : KBytes} {state : State} {chunk : KBytes}
    {result : Progress} (wf : input.wf = true) (held : state.InCarrier limits input)
    (incoming : Window input state.position chunk)
    (fed : feed limits state chunk = .ok result) :
    result.InCarrier limits input state chunk :=
  Proofs.Formats.Arrow.Framing.Incremental.feed_refines wf held incoming fed

/-- After all bytes have been supplied, successful finalization identifies
the original EOS at the exact end of the immutable reference. -/
theorem finish_refines {limits : Limits} {input : KBytes} {state : State} {last : Nat}
    (held : state.InCarrier limits input) (exhausted : state.position = input.len)
    (finished : finish state = .ok last) :
    last = input.len ∧ ∃ offset, offset + 8 = last ∧ readEnvelope limits input offset = .ok .eos :=
  Proofs.Formats.Arrow.Framing.Incremental.finish_refines held exhausted finished

/-- A later nonempty valid chunk after EOS fails at the first tail byte. -/
theorem feed_ended_tail {limits : Limits} {offset : Nat} {chunk : KBytes}
    (valid : chunk.wf = true) (nonempty : chunk.len ≠ 0) :
    feed limits (.ended offset) chunk = .error ⟨.tail, offset, .malformed .trailingBytes⟩ := by
  simp [feed, valid, nonempty]

/-- The first tail byte follows the original EOS, whether the same fragment
completed EOS or the reader reached it on an earlier fragment. -/
theorem feed_tail_exact {limits : Limits} {input chunk : KBytes} {state : State} {tail : Nat}
    (wf : input.wf = true) (held : state.InCarrier limits input)
    (incoming : Window input state.position chunk)
    (failed : feed limits state chunk = .error ⟨.tail, tail, .malformed .trailingBytes⟩) :
    let markerOf : State → Nat := fun
      | .prefix offset _ | .metadata offset _ _ | .body offset _ _ _ => offset
      | .ended offset => offset - 8
    let marker := markerOf state
    tail = marker + 8 ∧ tail < input.len ∧ readEnvelope limits input marker = .ok .eos :=
  Proofs.Formats.Arrow.Framing.Incremental.feed_tail_exact wf held incoming failed

/-- Supplying the first tail byte while completing the original EOS
necessarily produces the exact tail failure. -/
theorem feed_prefix_tail {limits : Limits} {input chunk : KBytes} {offset : Nat}
    {pending : Buffer 8} (wf : input.wf = true) (held : Window input offset pending.bytes)
    (incoming : Window input (offset + pending.bytes.len) chunk)
    (eos : readEnvelope limits input offset = .ok .eos)
    (offered : offset + 8 < offset + pending.bytes.len + chunk.len) :
    feed limits (.prefix offset pending) chunk =
      .error ⟨.tail, offset + 8, .malformed .trailingBytes⟩ :=
  Proofs.Formats.Arrow.Framing.Incremental.feed_prefix_tail wf held incoming eos offered

/-- At the declared input end, a short pending body has the original
truncated body slice and precise finish failure. -/
theorem finish_body_exact {limits : Limits} {input header : KBytes} {offset size : Nat}
    {pending : Buffer size} (wf : input.wf = true)
    (held : (State.body offset header size pending).InCarrier limits input)
    (exhausted : (State.body offset header size pending).position = input.len)
    (short : pending.bytes.len < size) :
    let bodyStart := offset + 8 + header.len
    readEnvelope limits input offset = .ok (.metadata header.len) ∧
      readBody limits input bodyStart size = .error (.malformed .truncated) ∧
      finish (.body offset header size pending) =
        .error ⟨.body, bodyStart, .malformed .truncated⟩ :=
  Proofs.Formats.Arrow.Framing.Incremental.finish_body_exact wf held exhausted short

/-- A valid fragment that leaves the body short is ordinary waiting. -/
theorem feed_body_wait {limits : Limits} {chunk header : KBytes} {offset size : Nat}
    {pending : Buffer size} (valid : chunk.wf = true)
    (short : pending.bytes.len + chunk.len < size) :
    feed limits (.body offset header size pending) chunk =
      .ok (.wait (.body offset header size (pending.feed chunk valid).buffered)) :=
  Proofs.Formats.Arrow.Framing.Incremental.feed_body_wait valid short

end Silmaril.Formats.Arrow.Framing.Incremental
