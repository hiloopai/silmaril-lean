module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Defs
import Silmaril.Formats.Arrow.Framing.Incremental.Thms
import Silmaril.Formats.Arrow.Framing.Thms
import Silmaril.Formats.Arrow.MixedFlat.Events.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Prelude.Bytes.Equiv.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open MixedFlat.Stream.Incremental
open Arrow.Framing.Incremental (Frame Window metadataBytes)

theorem decode_checked {limits : MixedFlat.Stream.Incremental.Limits} {fields : List MixedFlat.Field}
    {running : Running} {frame : Frame} {value : Delivered fields}
    (decoded : decode limits fields running frame = .ok value) :
    ∃ metadata,
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
        limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) = .ok metadata ∧
      running.ordinal < limits.mixed.observation.ipc.batches ∧
      value.dataBuffers = metadata.counts.sum ∧
      running.dataBuffers + value.dataBuffers ≤ limits.totalDataBuffers ∧
      Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
      MixedFlat.readParsed limits.mixed fields metadata
        (.leaf frame.body.len (frame.body.read 0 frame.body.len)) = .ok value.record.observed ∧
      value.record.range = frameRange frame := by
  unfold decode at decoded
  dsimp only at decoded
  split at decoded
  · contradiction
  rename_i batches
  cases metadataCheck : MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
      limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) with
  | error => simp [metadataCheck, bind, Except.bind, Except.mapError] at decoded
  | ok metadata =>
    simp only [metadataCheck, bind, Except.bind, Except.mapError] at decoded
    split at decoded
    · contradiction
    rename_i enough
    cases budget : Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) with
    | error => simp [budget] at decoded
    | ok budgetResult =>
      cases budgetResult
      simp only [budget] at decoded
      split at decoded
      · contradiction
      rename_i observed parsed
      simp only [pure, Except.pure, Except.ok.injEq] at decoded
      subst value
      exact ⟨metadata, rfl, by omega, rfl, Nat.le_of_not_gt enough, budget, parsed, rfl⟩

private theorem parsedExtent {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {observed : MixedFlat.Observed}
    (good : MixedFlat.readParsed limits fields metadata body = .ok observed) :
    metadata.bodyLength = body.len := by
  unfold MixedFlat.readParsed at good
  cases bound : MixedFlat.bindBatch limits fields metadata body with
  | error => simp [bound, bind, Except.bind] at good
  | ok plan => exact plan.extent

private theorem pack_window {len raw offset : Nat} {fragment : KBytes}
    (window : Window (.leaf len raw) offset fragment) :
    metadataBytes fragment = (KBytes.leaf len raw).slice offset fragment.len := by
  let ref := KBytes.leaf len raw
  let slice := ref.slice offset fragment.len
  have wf : ref.wf = true := rfl
  have same : fragment ≈ slice := window.exact.trans
    (ref.toList_slice offset fragment.len wf window.bounded).symm
  have sliceWf := ref.wf_slice offset fragment.len wf window.bounded
  have fit : 0 + fragment.len ≤ fragment.len := by simp
  have read := KBytes.read_congr window.source sliceWf same fit
  change KBytes.leaf fragment.len (fragment.read 0 fragment.len) = slice
  rw [read]
  simp [slice, ref, KBytes.slice, KBytes.read]

theorem schema_exact {ipc : Arrow.Limits} {len raw : Nat} {frame : Frame}
    {fields : List MixedFlat.Field}
    (original : frame.InCarrier ipc (.leaf len raw)) (first : frame.offset = 0)
    (checked : MixedFlat.readSchema ipc (metadataBytes frame.metadata) = .ok fields) :
    MixedFlat.Stream.readSchemaFrame ipc (.leaf len raw) = .ok (fields, 8 + frame.metadata.len) := by
  have schemaMatch := pack_window original.2.1
  have env := original.1
  rw [first] at env schemaMatch
  rw [schemaMatch] at checked
  simp [MixedFlat.Stream.readSchemaFrame, env, checked, bind, Except.bind,
    Except.mapError, pure, Except.pure]

theorem packed_frame {ipc : Arrow.Limits} {len raw : Nat} {frame : Frame}
    (original : frame.InCarrier ipc (.leaf len raw)) (bodyWf : frame.body.wf = true) :
    metadataBytes frame.metadata = (KBytes.leaf len raw).slice (frame.offset + 8) frame.metadata.len ∧
      readBody ipc (.leaf len raw) (frame.offset + 8 + frame.metadata.len) frame.body.len =
        .ok (metadataBytes frame.body) := by
  let start := frame.offset + 8 + frame.metadata.len
  let carrier := KBytes.leaf len raw
  obtain ⟨body, bodyRead, bodyBytes⟩ := original.2.2.2
  obtain ⟨_, _, _, fit, selected⟩ := (readBody_iff _ _ _ _ _).mp bodyRead
  have bodyWindow : Window carrier start frame.body :=
    ⟨bodyWf, fit, bodyBytes.trans (by rw [selected]; exact carrier.toList_slice start frame.body.len rfl fit)⟩
  have bodyMatch := (pack_window bodyWindow).trans selected.symm
  exact ⟨pack_window original.2.1, bodyMatch.symm ▸ bodyRead⟩

theorem record_exact {limits : MixedFlat.Stream.Incremental.Limits} {len raw : Nat}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame} {value : Delivered fields}
    (original : frame.InCarrier limits.mixed.observation.ipc (.leaf len raw))
    (bodyWf : frame.body.wf = true)
    (decoded : decode limits fields running frame = .ok value) :
    MixedFlat.Stream.readRecord limits.mixed (.leaf len raw) fields running.rows frame.offset
      frame.metadata.len = .ok value.record := by
  obtain ⟨metadata, metadataCheck, _, _, _, budget, parsed, range⟩ := decode_checked decoded
  have extent : metadata.bodyLength = frame.body.len := by
    exact parsedExtent (body := metadataBytes frame.body) parsed
  obtain ⟨metadataMatch, bodyRead⟩ := packed_frame original bodyWf
  rw [metadataMatch] at metadataCheck
  apply (MixedFlat.Stream.readRecord_iff _ _ _ _ _ _ _).mpr
  refine ⟨metadata, metadataBytes frame.body, metadataCheck, ?_, budget, parsed, ?_⟩
  · rw [extent]
    exact bodyRead
  · rw [range, extent]
    rfl

private theorem field_extent {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {metadata : MixedFlat.Metadata} {body : KBytes} {index : Nat} {cause : MixedFlat.ColumnError}
    (failed : MixedFlat.readParsed limits fields metadata body = .error (.field index cause)) :
    metadata.bodyLength = body.len := by
  by_cases extent : metadata.bodyLength = body.len
  · exact extent
  · by_cases source : body.wf = true
    · simp [MixedFlat.readParsed, MixedFlat.bindBatch, source, extent, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed
    · simp [MixedFlat.readParsed, MixedFlat.bindBatch, source, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed

theorem decode_field_checked {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame}
    {index : Nat} {cause : MixedFlat.ColumnError}
    (failed : decode limits fields running frame = .error (.record (.decode (.field index cause)))) :
    ∃ metadata,
      MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
        limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) = .ok metadata ∧
      running.ordinal < limits.mixed.observation.ipc.batches ∧
      running.dataBuffers + metadata.counts.sum ≤ limits.totalDataBuffers ∧
      Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) = .ok () ∧
      metadata.bodyLength = frame.body.len ∧
      MixedFlat.readParsed limits.mixed fields metadata (metadataBytes frame.body) = .error (.field index cause) := by
  unfold decode at failed
  dsimp only at failed
  split at failed
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at failed
  rename_i batches
  cases metadataCheck : MixedFlat.readMetadata limits.mixed.observation.ipc limits.mixed.view.dataBuffers
      limits.mixed.totalDataBuffers fields (metadataBytes frame.metadata) with
  | error => simp [metadataCheck, bind, Except.bind, Except.mapError] at failed
  | ok metadata =>
    simp only [metadataCheck, bind, Except.bind, Except.mapError] at failed
    split at failed
    · simp [throw, throwThe, MonadExceptOf.throw] at failed
    rename_i enough
    cases budget : Body.checkBudget limits.mixed.observation fields.length (running.rows + metadata.batch.rowCount) with
    | error => simp [budget] at failed
    | ok accepted =>
      cases accepted
      simp only [budget] at failed
      split at failed
      · rename_i fault parsed
        change (Except.error (.record (.decode fault)) : Except BatchError (Delivered fields)) = _ at failed
        simp only [Except.error.injEq, BatchError.record.injEq, MixedFlat.Stream.BatchError.decode.injEq] at failed
        subst fault
        exact ⟨metadata, rfl, by omega, Nat.le_of_not_gt enough, budget,
          field_extent (body := metadataBytes frame.body) parsed, parsed⟩
      · contradiction

private theorem aligned_eq {fields : List MixedFlat.Field} {observed : MixedFlat.Observed}
    {left right : MixedFlat.Events.Batch (MixedFlat.Events.schema fields)}
    (a : MixedFlat.Events.Agrees (MixedFlat.Events.schema fields) observed left)
    (b : MixedFlat.Events.Agrees (MixedFlat.Events.schema fields) observed right) : left = right := by
  have rows := a.1.symm.trans b.1
  have values : left.values = right.values := by
    funext i
    exact congrArg Prod.snd (Option.some.inj ((a.2.2 i).symm.trans (b.2.2 i)))
  exact AlignedColumns.ext rows values

theorem pull_exact {limits : MixedFlat.Stream.Incremental.Limits} {len raw : Nat}
    {fields : List MixedFlat.Field} {running : Running} {frame : Frame} {value : Delivered fields}
    (original : frame.InCarrier limits.mixed.observation.ipc (.leaf len raw))
    (bodyWf : frame.body.wf = true)
    (decoded : decode limits fields running frame = .ok value) :
    ∃ pulled,
      MixedFlat.Stream.Events.readNext limits.mixed (.leaf len raw) fields
        (limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal running.rows frame.offset =
        .ok (some pulled) ∧ pulled.record = value.record ∧ pulled.event = value.event := by
  obtain ⟨_, _, available, _, _, _, _, _⟩ := decode_checked decoded
  have remaining : limits.mixed.observation.ipc.batches - running.ordinal ≠ 0 := by omega
  have originalRecord := record_exact original bodyWf decoded
  let pulled : MixedFlat.Stream.Events.Decoded fields := ⟨value.record, value.event, value.aligned⟩
  simp only [MixedFlat.Stream.Events.readNext, original.1, Except.mapError, bind, Except.bind,
    remaining, ite_false]
  refine ⟨pulled, ?_, rfl, rfl⟩
  split
  · rename_i invalid failed
    rw [originalRecord] at failed
    contradiction
  · rename_i record checked
    have same := Except.ok.inj (checked.symm.trans originalRecord)
    subst record
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq]
    congr 1
    apply aligned_eq
    · exact MixedFlat.Events.ofObserved_agrees _ _ _ _
    · exact value.aligned

abbrev FramingState := Arrow.Framing.Incremental.State

def anchor : FramingState → Nat
  | .prefix offset _ | .metadata offset _ _ | .body offset _ _ _ => offset
  | .ended offset => offset - 8

theorem framing_shape {ipc : Arrow.Limits} {previous : FramingState} {chunk : KBytes}
    {reply : Arrow.Framing.Incremental.Progress}
    (fed : Arrow.Framing.Incremental.feed ipc previous chunk = .ok reply) :
    match reply with
    | .wait next | .advance next _ => anchor next = anchor previous
    | .frame frame next _ =>
      frame.offset = anchor previous ∧ anchor next = frame.next ∧ frame.body.wf = true := by
  unfold Arrow.Framing.Incremental.feed at fed
  split at fed
  · rename_i valid
    cases previous with
    | «prefix» offset pending =>
      dsimp only at fed
      split at fed
      · contradiction
      · split at fed
        · simp only [pure, Except.pure, Except.ok.injEq] at fed
          subst reply
          rfl
        · cases hdr : readPrefix ipc ((pending.feed chunk valid).buffered.bytes.read 0 4)
                ((pending.feed chunk valid).buffered.bytes.read 4 4) with
          | error =>
            simp [hdr, bind, Except.bind, Except.mapError] at fed
          | ok envelope =>
            cases envelope with
            | metadata size =>
              simp [hdr, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
              subst reply
              rfl
            | eos =>
              by_cases zero : (pending.feed chunk valid).rest.len = 0
              · simp [hdr, zero, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
                subst reply
                simp [anchor]
              · simp [hdr, zero, bind, Except.bind, Except.mapError, throw] at fed
    | metadata offset size pending =>
      dsimp only at fed
      split at fed
      · simp only [pure, Except.pure, Except.ok.injEq] at fed
        subst reply
        rfl
      · cases planned : Arrow.Framing.Incremental.plan ipc (pending.feed chunk valid).buffered.bytes with
        | error => simp [planned, bind, Except.bind, Except.mapError] at fed
        | ok size =>
          simp [planned, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
          subst reply
          rfl
    | body offset header size pending =>
      dsimp only at fed
      split at fed
      · simp only [pure, Except.pure, Except.ok.injEq] at fed
        subst reply
        rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at fed
        subst reply
        exact ⟨rfl, rfl, (pending.feed chunk valid).buffered.source⟩
    | ended offset =>
      dsimp only at fed
      split at fed
      · simp only [Except.ok.injEq] at fed
        subst reply
        rfl
      · contradiction
  · contradiction

theorem completed_frame_at {size packed : Nat} {cursor : Cursor} {chunk rest : KBytes}
    {frame : Frame} {next : FramingState}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (fed : Arrow.Framing.Incremental.feed cursor.limits.mixed.observation.ipc cursor.input chunk =
      .ok (.frame frame next rest)) :
    frame.offset = cursor.messageOffset ∧
      frame.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed) ∧ frame.body.wf = true :=
  ⟨(framing_shape fed).1, (Arrow.Framing.Incremental.feed_refines rfl held incoming fed).1,
    (framing_shape fed).2.2⟩

theorem feed_refines {size packed : Nat} {cursor : Cursor} {chunk : KBytes} {reply : Progress}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (incoming : Window (.leaf size packed) cursor.position chunk)
    (fed : feed cursor chunk = .ok reply) :
    reply.Refines size packed cursor chunk := by
  let ipc := cursor.limits.mixed.observation.ipc
  cases low : Arrow.Framing.Incremental.feed ipc cursor.input chunk with
  | error cause =>
    simp [feed, ipc, low, bind, Except.bind, Except.mapError] at fed
  | ok step =>
    have carrier := Arrow.Framing.Incremental.feed_refines rfl held incoming low
    have shape := framing_shape low
    cases step with
    | wait pending =>
      simp [feed, ipc, low, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
      subst reply
      exact ⟨carrier.1, rfl, rfl, shape, carrier.2⟩
    | advance pending rest =>
      simp [feed, ipc, low, bind, Except.bind, Except.mapError, pure, Except.pure] at fed
      subst reply
      exact ⟨⟨carrier.1, rfl, carrier.2.1, carrier.2.2⟩, rfl, shape⟩
    | frame frame pending rest =>
      obtain ⟨wire, heldNext, _, suffix, consumed⟩ := carrier
      obtain ⟨offset, nextOffset, bodyWf⟩ := shape
      change frame.offset = cursor.messageOffset at offset
      cases phase : cursor.phase with
      | schema =>
        cases schemaCheck : MixedFlat.readSchema ipc (metadataBytes frame.metadata) with
        | error =>
          simp [feed, ipc, low, phase, schemaCheck, bind, Except.bind, Except.mapError] at fed
        | ok fields =>
          by_cases empty : frame.body.len = 0
          · simp [feed, ipc, low, phase, schemaCheck, empty, bind, Except.bind, Except.mapError,
              pure, Except.pure] at fed
            subst reply
            refine ⟨⟨heldNext, rfl, suffix, consumed⟩, phase, rfl, nextOffset, ?_⟩
            intro initially
            have first : frame.offset = 0 := offset.trans initially
            simpa [frameRange, MixedFlat.Stream.BatchRange.next, MixedFlat.Stream.BatchRange.bodyStart, first, empty] using
              schema_exact wire first schemaCheck
          · simp [feed, ipc, low, phase, schemaCheck, empty, bind, Except.bind, Except.mapError,
              throw] at fed
      | records fields running =>
        cases decoded : decode cursor.limits fields running frame with
        | error =>
          simp [feed, ipc, low, phase, decoded, bind, Except.bind, Except.mapError] at fed
        | ok value =>
          simp [feed, ipc, low, phase, decoded, bind, Except.bind, Except.mapError,
            pure, Except.pure] at fed
          subst reply
          obtain ⟨_, _, _, _, _, _, _, recordRange⟩ := decode_checked decoded
          have atStart : value.record.range.offset = cursor.messageOffset := by
            simpa [recordRange, frameRange] using offset
          have atNext : anchor pending = value.record.range.next := by
            simpa [recordRange, frameRange, MixedFlat.Stream.BatchRange.next, MixedFlat.Stream.BatchRange.bodyStart, Frame.next]
              using nextOffset
          refine ⟨⟨heldNext, rfl, suffix, consumed⟩, running, phase, rfl, atStart, atNext, ?_⟩
          rw [← offset]
          exact pull_exact wire bodyWf decoded

theorem steps_agree {size packed : Nat} {fields : List MixedFlat.Field} {before last : Cursor}
    {batches : List (Delivered fields)} {running : Running}
    (steps : RecordSteps size packed fields before batches last)
    (held : before.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed))
    (phase : before.phase = .records fields running) :
    RecordAgreement size packed fields before running batches last := by
  induction steps generalizing running with
  | stop =>
    simp only [RecordAgreement, List.map_nil, List.nil_append]
    refine ⟨running, held, trivial, phase, .stop, ?_⟩
    cases MixedFlat.Stream.readBatches _ _ _ _ _ _ _ <;> rfl
  | wait incoming step _ ih =>
    obtain ⟨nextHeld, sameLimits, samePhase, sameOffset, _⟩ := feed_refines held incoming step
    rw [← sameLimits] at nextHeld
    simpa only [RecordAgreement, sameLimits, sameOffset] using ih nextHeld (samePhase.trans phase)
  | advance incoming step _ ih =>
    obtain ⟨⟨nextHeld, sameLimits, _, _⟩, samePhase, sameOffset⟩ := feed_refines held incoming step
    rw [← sameLimits] at nextHeld
    simpa only [RecordAgreement, sameLimits, sameOffset] using ih nextHeld (samePhase.trans phase)
  | @batch before next last chunk rest value batches incoming step _ ih =>
    obtain ⟨⟨nextHeld, sameLimits, _, _⟩, active, samePhase, nextPhase, _, nextOffset,
      pulled, read, sameRecord, sameEvent⟩ := feed_refines held incoming step
    have same : active = running := Phase.records.inj (samePhase.symm.trans phase) |>.2
    subst active
    rw [← sameLimits] at nextHeld
    obtain ⟨after, finalHeld, finalLimits, finalPhase, prefixSteps, eagerSuffix⟩ :=
      ih nextHeld nextPhase
    obtain ⟨fuel, remaining, eagerStep⟩ := MixedFlat.Stream.Events.readNext_record read
    have fuelExact : before.limits.mixed.observation.ipc.batches - (running.ordinal + 1) = fuel := by omega
    simp only [sameLimits, nextOffset] at finalHeld finalLimits prefixSteps eagerSuffix
    simp only [sameRecord] at eagerStep
    have rowCount := value.aligned.1
    rw [← rowCount] at prefixSteps eagerSuffix
    change MixedFlat.Stream.readBatches _ _ _ _ _ _ _ = _ at eagerSuffix
    rw [fuelExact] at prefixSteps eagerSuffix
    refine ⟨after, finalHeld, finalLimits, finalPhase, ?_, ?_⟩
    · rw [remaining]
      have tail : MixedFlat.Stream.Events.Prefix before.limits.mixed (.leaf size packed) fields
          fuel (running.ordinal + 1) (running.rows + pulled.record.observed.rowCount)
          pulled.record.range.next (batches.map Delivered.event)
          (before.limits.mixed.observation.ipc.batches - after.ordinal) after.ordinal after.rows
          last.messageOffset := by simpa only [sameRecord] using prefixSteps
      have stepRead : MixedFlat.Stream.Events.readNext before.limits.mixed (.leaf size packed) fields
          (fuel + 1) running.ordinal running.rows before.messageOffset = .ok (some pulled) := by
        simpa only [remaining] using read
      simpa only [List.map_cons, sameEvent] using MixedFlat.Stream.Events.Prefix.next stepRead tail
    · rw [eagerStep, eagerSuffix]
      simp only [List.map_cons]
      cases MixedFlat.Stream.readBatches _ _ _ _ _ _ _ <;> rfl

private theorem schemaSteps_agree {size packed : Nat} {fields : List MixedFlat.Field}
    {before opened : Cursor} (steps : SchemaSteps size packed fields before opened)
    (held : before.input.InCarrier before.limits.mixed.observation.ipc (.leaf size packed))
    (initial : before.messageOffset = 0) :
    SchemaAgreement size packed fields before.limits opened := by
  induction steps with
  | publish incoming step =>
    obtain ⟨⟨nextHeld, limits, _, _⟩, _, phase, offset, read⟩ := feed_refines held incoming step
    exact ⟨nextHeld, limits, phase, offset.symm ▸ read initial⟩
  | wait incoming step _ ih =>
    obtain ⟨nextHeld, limits, _, offset, _⟩ := feed_refines held incoming step
    rw [← limits] at nextHeld
    simpa only [limits] using ih nextHeld (offset.trans initial)
  | advance incoming step _ ih =>
    obtain ⟨⟨nextHeld, limits, _, _⟩, _, offset⟩ := feed_refines held incoming step
    rw [← limits] at nextHeld
    simpa only [limits] using ih nextHeld (offset.trans initial)

theorem open_agrees {size packed : Nat} {fields : List MixedFlat.Field} {limits : MixedFlat.Stream.Incremental.Limits}
    {opened : Cursor} (steps : SchemaSteps size packed fields (start limits) opened) :
    SchemaAgreement size packed fields limits opened :=
  schemaSteps_agree steps (Arrow.Framing.Incremental.start_refines (Nat.zero_le _)) rfl

theorem finish_agrees {size packed closedAt : Nat} {cursor : Cursor}
    {fields : List MixedFlat.Field} {running : Running}
    (held : cursor.input.InCarrier cursor.limits.mixed.observation.ipc (.leaf size packed))
    (phase : cursor.phase = .records fields running) (exhausted : cursor.position = size)
    (finished : finish cursor = .ok closedAt) :
    closedAt = size ∧
      MixedFlat.Stream.Events.readNext cursor.limits.mixed (.leaf size packed) fields
        (cursor.limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal running.rows
        cursor.messageOffset = .ok none ∧
      MixedFlat.Stream.readBatches cursor.limits.mixed (.leaf size packed) fields
        (cursor.limits.mixed.observation.ipc.batches - running.ordinal) running.ordinal running.rows
        cursor.messageOffset = .ok [] := by
  cases framed : Arrow.Framing.Incremental.finish cursor.input with
  | error => simp [finish, framed, bind, Except.bind, Except.mapError] at finished
  | ok observed =>
    simp [finish, framed, phase, bind, Except.bind, Except.mapError, pure, Except.pure] at finished
    subst observed
    obtain ⟨equal, offset, eosEnd, eos⟩ :=
      Arrow.Framing.Incremental.finish_refines held exhausted framed
    have eosOffset : cursor.messageOffset = offset := by
      cases input : cursor.input <;> simp [Arrow.Framing.Incremental.finish, input] at framed
      simp [Cursor.messageOffset, input]
      omega
    rw [eosOffset]
    have atEnd := eosEnd.trans equal
    refine ⟨equal, MixedFlat.Stream.Events.readNext_eos.mpr ⟨eos, atEnd⟩, ?_⟩
    simp [MixedFlat.Stream.readBatches, eos, atEnd, bind, Except.bind, Except.mapError, pure, Except.pure]

theorem complete_agrees {size packed closedAt : Nat} {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {opened last : Cursor} {batches : List (Delivered fields)}
    (opening : SchemaSteps size packed fields (start limits) opened)
    (records : RecordSteps size packed fields opened batches last)
    (exhausted : last.position = size) (finished : finish last = .ok closedAt) :
    closedAt = size ∧ MixedFlat.Stream.read limits.mixed (.leaf size packed) =
      .ok ⟨fields, batches.map Delivered.record⟩ := by
  obtain ⟨held, openedLimits, phase, schemaRead⟩ := open_agrees opening
  rw [← openedLimits] at held
  obtain ⟨running, finalHeld, finalLimits, finalPhase, _, eager⟩ := steps_agree records held phase
  rw [← finalLimits] at finalHeld
  obtain ⟨endAt, _, tail⟩ := finish_agrees finalHeld finalPhase exhausted finished
  simp only [finalLimits, openedLimits] at eager tail
  refine ⟨endAt, ?_⟩
  rw [tail] at eager
  simp only [Nat.sub_zero] at eager
  simp [MixedFlat.Stream.read, KBytes.wf, schemaRead, eager, bind, Except.bind, Except.map,
    pure, Except.pure]

private theorem drainPrefix {limits : MixedFlat.Limits} {input : KBytes} {fields : List MixedFlat.Field}
    {remaining ordinal rows offset available lastOrdinal lastRows lastOffset : Nat}
    {events : List (MixedFlat.Events.Batch (MixedFlat.Events.schema fields))}
    (delivered : MixedFlat.Stream.Events.Prefix limits input fields remaining ordinal rows offset events
      available lastOrdinal lastRows lastOffset)
    (ended : MixedFlat.Stream.Events.readNext limits input fields available lastOrdinal lastRows lastOffset =
      .ok none) (acc : List (MixedFlat.Events.Batch (MixedFlat.Events.schema fields))) :
    Arrow.Events.BatchReader.read.pull (MixedFlat.Stream.Events.reader limits) (MixedFlat.Events.schema fields)
      (remaining + 1) (.at input fields remaining ordinal rows offset) acc =
        ⟨acc.reverse ++ events, .eos⟩ := by
  induction delivered generalizing acc with
  | stop =>
    simp [Arrow.Events.BatchReader.read.pull, MixedFlat.Stream.Events.reader, ended, Except.map]
  | @next fuel ordinal rows offset decoded rest available lastOrdinal lastRows lastOffset read _ ih =>
    simpa [Arrow.Events.BatchReader.read.pull, MixedFlat.Stream.Events.reader, read, Except.map,
      List.reverse_cons, List.append_assoc] using ih ended (decoded.event :: acc)

theorem complete_pull_agrees {size packed closedAt : Nat} {limits : MixedFlat.Stream.Incremental.Limits}
    {fields : List MixedFlat.Field} {opened last : Cursor} {batches : List (Delivered fields)}
    (opening : SchemaSteps size packed fields (start limits) opened)
    (records : RecordSteps size packed fields opened batches last)
    (exhausted : last.position = size) (finished : finish last = .ok closedAt) :
    MixedFlat.Stream.Events.readAll limits.mixed (.leaf size packed) =
      .ok ⟨MixedFlat.Events.schema fields, ⟨batches.map Delivered.event, .eos⟩⟩ := by
  obtain ⟨held, openedLimits, phase, schemaRead⟩ := open_agrees opening
  rw [← openedLimits] at held
  obtain ⟨running, finalHeld, finalLimits, finalPhase, delivered, _⟩ := steps_agree records held phase
  rw [← finalLimits] at finalHeld
  obtain ⟨_, ended, _⟩ := finish_agrees finalHeld finalPhase exhausted finished
  rw [finalLimits] at ended
  have trace := drainPrefix delivered ended []
  simp only [openedLimits, Nat.sub_zero, List.reverse_nil, List.nil_append] at trace
  have openedInput : (MixedFlat.Stream.Events.reader limits.mixed).openInput (.leaf size packed) =
      .ok ⟨MixedFlat.Events.schema fields, .at (.leaf size packed) fields limits.mixed.observation.ipc.batches
        0 0 opened.messageOffset⟩ := by
    simp [MixedFlat.Stream.Events.reader, MixedFlat.Stream.Events.admit, KBytes.wf, schemaRead, Except.map,
      Except.mapError]
  rw [MixedFlat.Stream.Events.readAll, Arrow.Events.BatchReader.read, openedInput]
  simp [Except.map, trace]

theorem feed_late_failure {cursor : Cursor} {fields : List MixedFlat.Field} {running : Running}
    {chunk : KBytes} {cause : MixedFlat.Stream.Incremental.Error}
    (phase : cursor.phase = .records fields running) (failed : feed cursor chunk = .error cause) :
    let ipc := cursor.limits.mixed.observation.ipc
    (∃ framing, cause = .framing (some running.ordinal) framing ∧
      Arrow.Framing.Incremental.feed ipc cursor.input chunk = .error framing) ∨
    (∃ frame next rest typed, cause = .batch running.ordinal cursor.messageOffset typed ∧
      Arrow.Framing.Incremental.feed ipc cursor.input chunk = .ok (.frame frame next rest) ∧
      decode cursor.limits fields running frame = .error typed) := by
  dsimp only
  let ipc := cursor.limits.mixed.observation.ipc
  cases low : Arrow.Framing.Incremental.feed ipc cursor.input chunk with
  | error framing =>
    simp [feed, ipc, low, phase, Phase.ordinal, bind, Except.bind, Except.mapError] at failed
    exact .inl ⟨framing, failed.symm, rfl⟩
  | ok reply =>
    cases reply with
    | wait pending =>
      simp [feed, ipc, low, bind, Except.bind, Except.mapError, pure, Except.pure] at failed
    | advance pending rest =>
      simp [feed, ipc, low, bind, Except.bind, Except.mapError, pure, Except.pure] at failed
    | frame frame pending rest =>
      have offset : frame.offset = cursor.messageOffset := (framing_shape low).1
      cases decoded : decode cursor.limits fields running frame with
      | error typed =>
        simp [feed, ipc, low, phase, decoded, offset, bind, Except.bind, Except.mapError] at failed
        exact .inr ⟨frame, pending, rest, typed, failed.symm, rfl, decoded⟩
      | ok value =>
        simp [feed, ipc, low, phase, decoded, bind, Except.bind, Except.mapError, pure, Except.pure] at failed

end Silmaril.Proofs.Formats.Arrow.MixedFlat.Stream.Incremental
