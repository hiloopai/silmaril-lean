module

public import Silmaril.Formats.Arrow.Framing.Incremental.Defs
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Prelude.Bytes.Thms
import Silmaril.Prelude.Bytes.Equiv.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.Framing.Incremental

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Framing.Incremental

theorem buffer_feed {capacity : Nat} (buffer : Buffer capacity) (chunk : KBytes)
    (valid : chunk.wf = true) :
    let filled := buffer.feed chunk valid
    let bytes := buffer.bytes.toList ++ chunk.toList
    filled.buffered.bytes.toList = bytes.take capacity ∧
      filled.rest.toList = bytes.drop capacity ∧ filled.rest.wf = true := by
  let need := capacity - buffer.bytes.len
  let count := min need chunk.len
  have countFits : count ≤ chunk.len := Nat.min_le_right _ _
  have tailFits : count + (chunk.len - count) ≤ chunk.len := by omega
  have beforeLen := buffer.bytes.length_toList buffer.source
  have chunkLen := chunk.length_toList valid
  have beforeFits : buffer.bytes.toList.length ≤ capacity := beforeLen ▸ buffer.bounded
  change (if count = 0 then buffer.bytes else buffer.bytes ++ chunk.slice 0 count).toList =
      (buffer.bytes.toList ++ chunk.toList).take capacity ∧
    (chunk.slice count (chunk.len - count)).toList =
      (buffer.bytes.toList ++ chunk.toList).drop capacity ∧
    (chunk.slice count (chunk.len - count)).wf = true
  refine ⟨?_, ?_, chunk.wf_slice count _ valid tailFits⟩
  · rw [List.take_append, List.take_of_length_le beforeFits, beforeLen]
    have sameTake : chunk.toList.take count = chunk.toList.take need := by
      change chunk.toList.take (min need chunk.len) = chunk.toList.take need
      rw [← chunkLen]
      exact (List.take_eq_take_min).symm
    by_cases zero : count = 0
    · rw [ite_eq_left zero, ← sameTake, zero, List.take_zero, List.append_nil]
    · rw [ite_eq_right zero, KBytes.toList_append, KBytes.toList_slice chunk 0 count valid (by simpa using countFits),
        List.drop_zero, sameTake]
  · have dropped : buffer.bytes.toList.drop capacity = [] := List.drop_eq_nil_iff.mpr beforeFits
    rw [KBytes.toList_slice chunk count _ valid tailFits, List.drop_append, dropped,
      List.nil_append, beforeLen]
    have whole := List.length_drop (l := chunk.toList) (i := count)
    rw [chunkLen] at whole
    rw [List.take_of_length_le (Nat.le_of_eq whole)]
    change chunk.toList.drop count = chunk.toList.drop need
    by_cases needFits : need ≤ chunk.len
    · simp [count, Nat.min_eq_left needFits]
    · have atEnd : chunk.len ≤ need := by omega
      rw [show count = chunk.len from Nat.min_eq_right atEnd, ← chunkLen,
        List.drop_eq_nil_iff.mpr (Nat.le_refl _), List.drop_eq_nil_iff.mpr (chunkLen ▸ atEnd)]

private theorem emptyWindow (input : KBytes) (offset : Nat) (bounded : offset ≤ input.len) :
    Window input offset KBytes.empty := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa [KBytes.empty, KBytes.len] using bounded
  · rfl

theorem start_refines {limits : Limits} {input : KBytes} {offset : Nat} (bounded : offset ≤ input.len) :
    (start offset).InCarrier limits input :=
  emptyWindow input offset bounded

theorem feedWindow {input chunk : KBytes} {offset capacity : Nat} (wf : input.wf = true)
    (buffer : Buffer capacity) (valid : chunk.wf = true)
    (held : Window input offset buffer.bytes)
    (incoming : Window input (offset + buffer.bytes.len) chunk) :
    let filled := buffer.feed chunk valid
    Window input offset filled.buffered.bytes ∧
      Window input (offset + filled.buffered.bytes.len) filled.rest ∧
      filled.buffered.bytes.len + filled.rest.len = buffer.bytes.len + chunk.len ∧
      (filled.buffered.bytes.len < capacity → filled.rest.len = 0) := by
  let filled := buffer.feed chunk valid
  let total := buffer.bytes.len + chunk.len
  let source := input.toList.drop offset
  have bounds : offset + total ≤ input.len := by
    have h := incoming.bounded
    dsimp [total]
    omega
  have room : total ≤ source.length := by
    simp [source, KBytes.length_toList input wf]
    omega
  have contiguous : buffer.bytes.toList ++ chunk.toList = source.take total := by
    rw [held.exact, incoming.exact]
    change source.take buffer.bytes.len ++ (input.toList.drop (offset + buffer.bytes.len)).take chunk.len =
      source.take total
    rw [show input.toList.drop (offset + buffer.bytes.len) = source.drop buffer.bytes.len by
      simp [source], ← List.take_add]
  obtain ⟨prefixBytes, suffixBytes, suffixWf⟩ := buffer_feed buffer chunk valid
  change filled.buffered.bytes.toList = _ at prefixBytes
  change filled.rest.toList = _ at suffixBytes
  rw [contiguous] at prefixBytes suffixBytes
  have prefixLen : filled.buffered.bytes.len = min capacity total := by
    rw [← KBytes.length_toList _ filled.buffered.source, prefixBytes, List.length_take,
      List.length_take_of_le room]
  have suffixLen : filled.rest.len = total - capacity := by
    rw [← KBytes.length_toList _ suffixWf, suffixBytes, List.length_drop, List.length_take_of_le room]
  have cap : min capacity total ≤ total := Nat.min_le_right _ _
  have lengths : filled.buffered.bytes.len + filled.rest.len = total := by omega
  change Window input offset filled.buffered.bytes ∧
    Window input (offset + filled.buffered.bytes.len) filled.rest ∧
    filled.buffered.bytes.len + filled.rest.len = total ∧
    (filled.buffered.bytes.len < capacity → filled.rest.len = 0)
  have endFirst : offset + filled.buffered.bytes.len ≤ input.len := by omega
  have endRest : offset + filled.buffered.bytes.len + filled.rest.len ≤ input.len := by omega
  have noRest : filled.buffered.bytes.len < capacity → filled.rest.len = 0 := by omega
  refine ⟨⟨filled.buffered.source, endFirst, ?_⟩, ⟨suffixWf, endRest, ?_⟩, lengths, noRest⟩
  · rw [prefixBytes, List.take_take, prefixLen]
  · rw [suffixBytes, List.drop_take, suffixLen]
    change (source.drop capacity).take (total - capacity) =
      (input.toList.drop (offset + filled.buffered.bytes.len)).take (total - capacity)
    by_cases fits : capacity ≤ total
    · rw [prefixLen, Nat.min_eq_left fits, ← List.drop_drop]
    · have zero : total - capacity = 0 := by omega
      simp [zero]

private theorem word {input bytes : KBytes} {offset start width : Nat}
    (wf : input.wf = true) (window : Window input offset bytes) (fits : start + width ≤ bytes.len) :
    bytes.read start width = input.read (offset + start) width := by
  have bound := window.bounded
  rw [KBytes.read_eq bytes _ _ window.source fits, KBytes.read_eq input _ _ wf (by omega),
    window.exact, List.drop_take, List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

private theorem planSame {limits : Limits} {a b : KBytes} (wa : a.wf = true) (wb : b.wf = true)
    (same : a.toList = b.toList) : plan limits a = plan limits b := by
  have length := KBytes.len_eq_of_equiv wa wb (KBytes.equiv_iff.mpr same)
  have values := KBytes.read_congr wa wb (KBytes.equiv_iff.mpr same)
    (off := 0) (w := a.len) (by simp)
  unfold plan metadataBytes
  rw [← length, values]

private theorem envelopeMetadata {limits : Limits} {input : KBytes} {offset size : Nat}
    (aligned : offset % 8 = 0) (fits : offset + 8 + size ≤ input.len)
    (header : readPrefix limits (input.read offset 4) (input.read (offset + 4) 4) = .ok (.metadata size)) :
    readEnvelope limits input offset = .ok (.metadata size) := by
  simp [readEnvelope, aligned, Nat.not_lt.mpr (show offset + 8 ≤ input.len by omega), header,
    Nat.not_lt.mpr fits]

private theorem planBody {limits : Limits} {header : KBytes} {size : Nat}
    (planned : plan limits header = .ok size) : size % 8 = 0 ∧ size ≤ limits.bodyBytes := by
  unfold plan at planned
  cases message : frameBodyLength limits (metadataBytes header) with
  | error => simp [message, bind, Except.bind] at planned
  | ok declared =>
    by_cases aligned : declared % 8 = 0
    · by_cases over : limits.bodyBytes < declared
      · simp [message, aligned, over, bind, Except.bind, throw] at planned
      · simp [message, aligned, over, bind, Except.bind, pure, Except.pure] at planned
        subst size
        exact ⟨aligned, Nat.le_of_not_gt over⟩
    · simp [message, aligned, bind, Except.bind, throw] at planned

theorem feed_refines {limits : Limits} {input : KBytes} {state : State} {chunk : KBytes}
    {result : Progress} (wf : input.wf = true) (held : state.InCarrier limits input)
    (incoming : Window input state.position chunk)
    (fed : feed limits state chunk = .ok result) :
    result.InCarrier limits input state chunk := by
  have valid := incoming.source
  cases state with
  | «prefix» offset pending =>
    let filled := pending.feed chunk valid
    obtain ⟨collected, rest, extent, shortRest⟩ :=
      feedWindow wf pending valid held incoming
    change Window input (offset) filled.buffered.bytes at collected
    change Window input ((offset) + filled.buffered.bytes.len) filled.rest at rest
    change filled.buffered.bytes.len + filled.rest.len = pending.bytes.len + chunk.len at extent
    change (filled.buffered.bytes.len < 8 → filled.rest.len = 0) at shortRest
    by_cases aligned : offset % 8 = 0
    · by_cases short : filled.buffered.bytes.len < 8
      · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
          pure, Except.pure] at fed
        subst result
        have noRest := shortRest short
        refine ⟨collected, ?_⟩
        change offset + filled.buffered.bytes.len = offset + pending.bytes.len + chunk.len
        omega
      · have full : filled.buffered.bytes.len = 8 :=
          Nat.le_antisymm filled.buffered.bounded (Nat.le_of_not_gt short)
        have marker := word wf collected (start := 0) (width := 4) (by rw [full]; decide)
        have count := word wf collected (start := 4) (width := 4) (by rw [full]; decide)
        rw [Nat.add_zero] at marker
        cases parsed : readPrefix limits (filled.buffered.bytes.read 0 4)
            (filled.buffered.bytes.read 4 4) with
        | error cause =>
          simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
            parsed, bind, Except.bind, Except.mapError] at fed
        | ok observed =>
          cases observed with
          | metadata size =>
            simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
              parsed, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
            subst result
            rw [marker, count] at parsed
            have bound := collected.bounded
            have atMetadata := emptyWindow input (offset + 8) (by omega)
            refine ⟨⟨aligned, parsed, atMetadata⟩, ?_, ?_⟩
            · change Window input (offset + 8 + 0) filled.rest
              rw [Nat.add_zero]
              simpa only [full] using rest
            · change offset + 8 + 0 + filled.rest.len = offset + pending.bytes.len + chunk.len
              omega
          | eos =>
            by_cases empty : filled.rest.len = 0
            · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
                parsed, empty, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
              subst result
              rw [marker, count] at parsed
              have bound := collected.bounded
              have envelope : readEnvelope limits input offset = .ok .eos := by
                simp [readEnvelope, aligned,
                  Nat.not_lt.mpr (show offset + 8 ≤ input.len by omega), parsed]
              refine ⟨⟨offset, rfl, envelope⟩, ?_, ?_⟩
              · change Window input (offset + 8) filled.rest
                simpa only [full] using rest
              · change offset + 8 + filled.rest.len = offset + pending.bytes.len + chunk.len
                omega
            · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
                parsed, empty, bind, Except.bind, Except.mapError, throw] at fed
    · simp [feed, valid, aligned, bind, Except.bind, throw] at fed
  | metadata offset size pending =>
    obtain ⟨aligned, headerCheck, held⟩ := held
    let filled := pending.feed chunk valid
    obtain ⟨collected, rest, extent, shortRest⟩ :=
      feedWindow wf pending valid held incoming
    change Window input (offset + 8) filled.buffered.bytes at collected
    change Window input ((offset + 8) + filled.buffered.bytes.len) filled.rest at rest
    change filled.buffered.bytes.len + filled.rest.len = pending.bytes.len + chunk.len at extent
    change (filled.buffered.bytes.len < size → filled.rest.len = 0) at shortRest
    by_cases short : filled.buffered.bytes.len < size
    · simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short,
        pure, Except.pure] at fed
      subst result
      have noRest := shortRest short
      refine ⟨⟨aligned, headerCheck, collected⟩, ?_⟩
      change offset + 8 + filled.buffered.bytes.len = offset + 8 + pending.bytes.len + chunk.len
      omega
    · have full : filled.buffered.bytes.len = size :=
        Nat.le_antisymm filled.buffered.bounded (Nat.le_of_not_gt short)
      cases body : plan limits filled.buffered.bytes with
      | error cause =>
        simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short, body,
          bind, Except.bind, Except.mapError] at fed
      | ok bodyLength =>
        simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short, body,
          bind, Except.bind, Except.mapError, pure, Except.pure] at fed
        subst result
        have bound := collected.bounded
        have envelope : readEnvelope limits input offset = .ok (.metadata filled.buffered.bytes.len) := by
          rw [full]
          exact envelopeMetadata aligned (by omega) headerCheck
        refine ⟨⟨envelope, collected, body, emptyWindow input _ bound⟩, ?_, ?_⟩
        · change Window input (offset + 8 + filled.buffered.bytes.len + 0) filled.rest
          rwa [Nat.add_zero]
        · change offset + 8 + filled.buffered.bytes.len + 0 + filled.rest.len =
            offset + 8 + pending.bytes.len + chunk.len
          omega
  | body offset header size pending =>
    obtain ⟨envelope, headerWindow, planned, held⟩ := held
    let filled := pending.feed chunk valid
    obtain ⟨collected, rest, extent, shortRest⟩ :=
      feedWindow wf pending valid held incoming
    change Window input (offset + 8 + header.len) filled.buffered.bytes at collected
    change Window input ((offset + 8 + header.len) + filled.buffered.bytes.len) filled.rest at rest
    change filled.buffered.bytes.len + filled.rest.len = pending.bytes.len + chunk.len at extent
    change (filled.buffered.bytes.len < size → filled.rest.len = 0) at shortRest
    by_cases short : filled.buffered.bytes.len < size
    · simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short,
        pure, Except.pure] at fed
      subst result
      have noRest := shortRest short
      refine ⟨⟨envelope, headerWindow, planned, collected⟩, ?_⟩
      change offset + 8 + header.len + filled.buffered.bytes.len =
        offset + 8 + header.len + pending.bytes.len + chunk.len
      omega
    · simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short,
        pure, Except.pure] at fed
      subst result
      have full : filled.buffered.bytes.len = size :=
        Nat.le_antisymm filled.buffered.bounded (Nat.le_of_not_gt short)
      have metadataMatch := planSame (limits := limits) headerWindow.source
        (input.wf_slice (offset + 8) header.len wf headerWindow.bounded)
        (headerWindow.exact.trans (input.toList_slice _ _ wf headerWindow.bounded).symm)
      obtain ⟨markerAligned, _, _, _, _, _, lengthAligned, _, _⟩ :=
        (readEnvelope_iff limits input offset (.metadata header.len) wf).mp envelope
      obtain ⟨bodyAligned, budget⟩ := planBody planned
      have bodyOffset : (offset + 8 + header.len) % 8 = 0 := by omega
      let actual := input.slice (offset + 8 + header.len) filled.buffered.bytes.len
      have bodyBound := collected.bounded
      have readActual : readBody limits input (offset + 8 + header.len)
          filled.buffered.bytes.len = .ok actual := by
        apply (readBody_iff _ _ _ _ _).mpr
        exact ⟨bodyOffset, by rwa [full], by rwa [full], bodyBound, rfl⟩
      refine ⟨⟨envelope, headerWindow, ?_, actual, readActual, ?_⟩, ?_, ?_, ?_, ?_⟩
      · rw [← metadataMatch, planned, full]
      · exact collected.exact.trans (input.toList_slice _ _ wf bodyBound).symm
      · exact emptyWindow input _ bodyBound
      · exact Nat.add_zero _
      · change Window input (offset + 8 + header.len + filled.buffered.bytes.len + 0) filled.rest
        rwa [Nat.add_zero]
      · change offset + 8 + header.len + filled.buffered.bytes.len + 0 + filled.rest.len =
          offset + 8 + header.len + pending.bytes.len + chunk.len
        omega
  | ended offset =>
    by_cases empty : chunk.len = 0
    · simp [feed, valid, empty] at fed
      subst result
      exact ⟨held, by simp [State.position, empty]⟩
    · simp [feed, valid, empty] at fed

theorem finish_refines {limits : Limits} {input : KBytes} {state : State} {last : Nat}
    (held : state.InCarrier limits input) (exhausted : state.position = input.len)
    (finished : finish state = .ok last) :
    last = input.len ∧ ∃ offset, offset + 8 = last ∧ readEnvelope limits input offset = .ok .eos := by
  cases state <;> simp [finish] at finished
  rename_i offset
  subst last
  obtain ⟨startOffset, endAt, envelope⟩ := held
  exact ⟨exhausted, startOffset, endAt.symm, envelope⟩

theorem feed_tail_exact {limits : Limits} {input chunk : KBytes} {state : State} {tail : Nat}
    (wf : input.wf = true) (held : state.InCarrier limits input)
    (incoming : Window input state.position chunk)
    (failed : feed limits state chunk = .error ⟨.tail, tail, .malformed .trailingBytes⟩) :
    let markerOf : State → Nat := fun
      | .prefix offset _ | .metadata offset _ _ | .body offset _ _ _ => offset
      | .ended offset => offset - 8
    let marker := markerOf state
    tail = marker + 8 ∧ tail < input.len ∧ readEnvelope limits input marker = .ok .eos := by
  have valid := incoming.source
  cases state <;> dsimp only
  case «prefix» offset pending =>
    let filled := pending.feed chunk valid
    by_cases aligned : offset % 8 = 0
    · by_cases short : filled.buffered.bytes.len < 8
      · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
          pure, Except.pure] at failed
      · cases header : readPrefix limits (filled.buffered.bytes.read 0 4)
            (filled.buffered.bytes.read 4 4) with
        | error cause =>
          simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
            header, bind, Except.bind, Except.mapError] at failed
        | ok result =>
          cases result with
          | metadata size =>
            simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
              header, bind, Except.bind, Except.mapError, pure, Except.pure] at failed
          | eos =>
            by_cases empty : filled.rest.len = 0
            · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
                header, empty, bind, Except.bind, Except.mapError, pure, Except.pure] at failed
            · simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, short,
                header, empty, bind, Except.bind, Except.mapError, throw, throwThe, MonadExceptOf.throw] at failed
              obtain ⟨collected, rest, _, _⟩ := feedWindow wf pending valid held incoming
              have full : filled.buffered.bytes.len = 8 :=
                Nat.le_antisymm filled.buffered.bounded (Nat.le_of_not_gt short)
              change Window input offset filled.buffered.bytes at collected
              change Window input (offset + filled.buffered.bytes.len) filled.rest at rest
              have marker := word wf collected (start := 0) (width := 4) (by rw [full]; decide)
              have size := word wf collected (start := 4) (width := 4) (by rw [full]; decide)
              rw [Nat.add_zero] at marker
              rw [marker, size] at header
              have bounded := rest.bounded
              have tailFits : offset + 8 < input.len := by omega
              exact ⟨failed.symm, by omega,
                by simp [readEnvelope, aligned, Nat.not_lt.mpr (Nat.le_of_lt tailFits), header]⟩
    · simp [feed, valid, aligned, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed
  case metadata offset size pending =>
    let filled := pending.feed chunk valid
    by_cases short : filled.buffered.bytes.len < size
    · simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short,
        pure, Except.pure] at failed
    · cases planned : plan limits filled.buffered.bytes <;>
        simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short, planned,
          bind, Except.bind, Except.mapError, pure, Except.pure] at failed
  case body offset header size pending =>
    let filled := pending.feed chunk valid
    by_cases short : filled.buffered.bytes.len < size <;>
      simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, short, pure, Except.pure] at failed
  case ended endAt =>
    by_cases empty : chunk.len = 0
    · simp [feed, valid, empty] at failed
    · simp [feed, valid, empty] at failed
      obtain ⟨marker, afterMarker, envelope⟩ := held
      have bounded := incoming.bounded
      change endAt + chunk.len ≤ input.len at bounded
      have markerExact : endAt - 8 = marker := by omega
      refine ⟨by omega, by omega, ?_⟩
      change readEnvelope limits input (endAt - 8) = .ok .eos
      rwa [markerExact]

theorem feed_prefix_tail {limits : Limits} {input chunk : KBytes} {offset : Nat}
    {pending : Buffer 8} (wf : input.wf = true) (held : Window input offset pending.bytes)
    (incoming : Window input (offset + pending.bytes.len) chunk)
    (eos : readEnvelope limits input offset = .ok .eos)
    (offered : offset + 8 < offset + pending.bytes.len + chunk.len) :
    feed limits (.prefix offset pending) chunk =
      .error ⟨.tail, offset + 8, .malformed .trailingBytes⟩ := by
  have valid := incoming.source
  let filled := pending.feed chunk valid
  obtain ⟨collected, _, extent, shortRest⟩ := feedWindow wf pending valid held incoming
  change Window input offset filled.buffered.bytes at collected
  change filled.buffered.bytes.len + filled.rest.len = pending.bytes.len + chunk.len at extent
  change (filled.buffered.bytes.len < 8 → filled.rest.len = 0) at shortRest
  have full : filled.buffered.bytes.len = 8 := by
    have bounded := filled.buffered.bounded
    by_cases short : filled.buffered.bytes.len < 8
    · have empty := shortRest short
      omega
    · omega
  have nonempty : filled.rest.len ≠ 0 := by omega
  have marker := word wf collected (start := 0) (width := 4) (by rw [full]; decide)
  have count := word wf collected (start := 4) (width := 4) (by rw [full]; decide)
  rw [Nat.add_zero] at marker
  obtain ⟨aligned, bounded, continuation, lengthZero⟩ := (readEnvelope_iff _ _ _ _ wf).mp eos
  rw [KBytes.length_toList input wf] at bounded
  change KBytes.leVal ((input.toList.drop offset).take 4) = 0xffffffff at continuation
  change KBytes.leVal ((input.toList.drop (offset + 4)).take 4) = 0 at lengthZero
  rw [← KBytes.read_eq input offset 4 wf (by omega)] at continuation
  rw [← KBytes.read_eq input (offset + 4) 4 wf (by omega)] at lengthZero
  have header : readPrefix limits (filled.buffered.bytes.read 0 4)
      (filled.buffered.bytes.read 4 4) = .ok .eos := by
    simp [marker, count, continuation, lengthZero, readPrefix]
  have long : ¬filled.buffered.bytes.len < 8 := by omega
  simp [feed, valid, aligned, ← show filled = pending.feed chunk valid from rfl, long,
    header, nonempty, bind, Except.bind, Except.mapError, throw, throwThe, MonadExceptOf.throw]

theorem finish_body_exact {limits : Limits} {input header : KBytes} {offset size : Nat}
    {pending : Buffer size} (wf : input.wf = true)
    (held : (State.body offset header size pending).InCarrier limits input)
    (exhausted : (State.body offset header size pending).position = input.len)
    (short : pending.bytes.len < size) :
    let bodyStart := offset + 8 + header.len
    readEnvelope limits input offset = .ok (.metadata header.len) ∧
      readBody limits input bodyStart size = .error (.malformed .truncated) ∧
      finish (.body offset header size pending) =
        .error ⟨.body, bodyStart, .malformed .truncated⟩ := by
  obtain ⟨envelope, _, planned, _⟩ := held
  obtain ⟨startAligned, _, _, _, _, _, metadataAligned, _, _⟩ :=
    (readEnvelope_iff _ _ _ _ wf).mp envelope
  obtain ⟨bodyAligned, budget⟩ := planBody planned
  change offset + 8 + header.len + pending.bytes.len = input.len at exhausted
  have atBody : (offset + 8 + header.len) % 8 = 0 := by omega
  have cutoff : input.len < offset + 8 + header.len + size := by omega
  exact ⟨envelope, by simp [readBody, atBody, bodyAligned, Nat.not_lt.mpr budget, cutoff], rfl⟩

theorem feed_body_wait {limits : Limits} {chunk header : KBytes} {offset size : Nat}
    {pending : Buffer size} (valid : chunk.wf = true)
    (short : pending.bytes.len + chunk.len < size) :
    feed limits (.body offset header size pending) chunk =
      .ok (.wait (.body offset header size (pending.feed chunk valid).buffered)) := by
  let filled := pending.feed chunk valid
  have same := (buffer_feed pending chunk valid).1
  change filled.buffered.bytes.toList = (pending.bytes.toList ++ chunk.toList).take size at same
  have length := congrArg List.length same
  rw [KBytes.length_toList _ filled.buffered.source, List.length_take, List.length_append,
    KBytes.length_toList _ pending.source, KBytes.length_toList _ valid,
    Nat.min_eq_right (Nat.le_of_lt short)] at length
  have stillShort : filled.buffered.bytes.len < size := by omega
  simp [feed, valid, ← show filled = pending.feed chunk valid from rfl, stillShort, pure, Except.pure]

end Silmaril.Proofs.Formats.Arrow.Framing.Incremental
