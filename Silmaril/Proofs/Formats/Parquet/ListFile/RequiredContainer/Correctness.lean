module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Defs
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer
open Silmaril.Formats.Parquet.ListPage (Event Row)
open Silmaril.Relational

public theorem openFile_repetition {limits : ListFile.Limits} {source : Bytes} {checked : Checked}
    (h : openFile limits source = .ok checked) :
    checked.shape.outer.repetition = some .required ∧ checked.shape.element.repetition = some .optional :=
  ListFile.admittedFor_repetition (ListFile.openFileFor_wire h).shape.2

public theorem readEvent_wire {entry : Triple} {event : Event}
    (h : readEvent entry = .ok event) : eventWire event = some entry := by
  unfold readEvent at h
  split at h <;> cases h <;> rfl

private theorem readEvents_wire {entries : List (Nat × Nat × Option Int32)} {events : List Event}
    (h : entries.mapM readEvent = .ok events) : events.map eventWire = entries.map some := by
  induction entries generalizing events with
  | nil => cases h; rfl
  | cons entry rest ih =>
    simp only [List.mapM_cons] at h
    cases first : readEvent entry with
    | error => simp [first, bind, Except.bind] at h
    | ok event =>
      simp only [first, bind, Except.bind] at h
      cases tail : rest.mapM readEvent with
      | error => rw [tail] at h; cases h
      | ok out =>
        rw [tail] at h
        obtain rfl := Except.ok.inj h
        simp [readEvent_wire first, ih tail]

public theorem decodeSections_wire {limits : ListPage.Limits} {slots : Nat}
    {repetition definition scalars : Bytes} {events : List Event}
    (h : decodeSections limits slots repetition definition scalars = .ok events) :
    SectionsWire slots repetition definition scalars events := by
  unfold decodeSections at h
  cases repRead : Hybrid.decode 1 slots limits.levels repetition with
  | error => simp [repRead, Except.mapError, bind, Except.bind] at h
  | ok reps =>
    simp only [repRead, Except.mapError, bind, Except.bind] at h
    cases defRead : Hybrid.decode 2 slots limits.levels definition with
    | error => simp [defRead] at h
    | ok defs =>
      simp only [defRead] at h
      split at h
      · contradiction
      cases read : Plain.decodeInt32 ((valueMask defs).count true) scalars with
      | error => simp [read] at h
      | ok values =>
        simp only [read] at h
        cases filled : FlatPage.reconstruct (valueMask defs) values with
        | error => simp [filled] at h
        | ok entries =>
          simp only [filled] at h
          cases actual : (reps.zip (defs.zip entries)).mapM readEvent with
          | error e => simp [actual] at h
          | ok decoded =>
            simp only [actual] at h
            obtain rfl := Except.ok.inj h
            have exactEvents := readEvents_wire actual
            obtain ⟨mask, ordered⟩ := FlatPage.reconstruct_ok_iff.mp filled
            have repCount := Hybrid.decode_length repRead
            have defCount := Hybrid.decode_length defRead
            have entryCount : entries.length = slots := by
              simpa [valueMask, defCount] using congrArg List.length mask
            have slotsExact : decoded.length = slots := by
              simpa [repCount, defCount, entryCount] using congrArg List.length exactEvents
            exact ⟨slotsExact, reps, defs, values, entries,
              (Hybrid.decode_ok_iff.mp repRead).2.2.2.2, (Hybrid.decode_ok_iff.mp defRead).2.2.2.2,
              repCount, defCount, entryCount, read, mask, ordered, exactEvents⟩

public theorem decodeEvents_wire {limits : ListPage.Limits} {slots : Nat} {body : Bytes}
    {events : List Event} (h : decodeEvents limits slots body = .ok events) :
    EventsWire limits slots body events := by
  unfold decodeEvents at h
  split at h
  · cases h
  rename_i bodyCap
  cases repSplit : FlatPage.splitV1Optional limits.levels.bytes body with
  | error => simp [repSplit, Except.mapError, bind, Except.bind] at h
  | ok first =>
    simp only [repSplit, Except.mapError, bind, Except.bind] at h
    cases defSplit : FlatPage.splitV1Optional limits.levels.bytes first.scalars with
    | error => simp [defSplit] at h
    | ok second =>
      simp only [defSplit] at h
      obtain ⟨repLength, repWidth, repBytes, _, fromBody⟩ := FlatPage.splitV1Optional_ok_iff.mp repSplit
      obtain ⟨defLength, defWidth, defBytes, _, fromRest⟩ := FlatPage.splitV1Optional_ok_iff.mp defSplit
      exact ⟨Nat.le_of_not_gt bodyCap, repLength, defLength, first.definitions, second.definitions,
        second.scalars, repWidth, defWidth, repBytes, defBytes,
        by simpa [fromRest, List.append_assoc] using fromBody, decodeSections_wire h⟩

private theorem noNullEvent {limits : ListPage.Limits} {slots : Nat} {body : Bytes}
    {events : List Event} (wire : EventsWire limits slots body events) :
    Event.nullList ∉ events := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, sections⟩ := wire.data
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ordered⟩ := sections.data
  intro member
  have invalid : none ∈ events.map eventWire := List.mem_map.mpr ⟨.nullList, member, rfl⟩
  rw [ordered] at invalid
  simp at invalid

public theorem readFrame_wire {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (h : readFrame checked framed frame = .ok rows) : FrameWire checked framed frame rows := by
  unfold readFrame at h
  split at h
  · contradiction
  cases sliced : checked.snapshot.bytes.slice? frame.payload.start (some frame.payload.stop) with
  | none => simp [sliced] at h
  | some body =>
    simp only [sliced] at h
    cases header : ListPage.checkV1 framed.chunk.metadata.codec frame.value body with
    | error err => simp [header, Except.mapError, Bind.bind, Except.bind] at h
    | ok info =>
      simp only [header, Except.mapError, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      rename_i slots
      split at h
      · contradiction
      rename_i rowCap
      cases decoded : decodeEvents checked.limits.page info.numValues body with
      | error err => simp [decoded] at h
      | ok events =>
        simp only [decoded] at h
        cases assembled : ListPage.reconstruct events with
        | error err => simp [assembled] at h
        | ok output =>
          simp only [assembled] at h
          split at h
          · contradiction
          rename_i count
          obtain rfl := Except.ok.inj h
          have order := ListPage.reconstruct_wire assembled
          have wire := decodeEvents_wire decoded
          refine ⟨?_, body, info, sliced, ListPage.checkV1_wire header, not_not.mp slots,
            Nat.le_of_not_gt rowCap, not_not.mp count, order ▸ wire⟩
          intro row member
          cases row with
          | some children => rfl
          | none =>
            have absent : Event.nullList ∈ events := by
              rw [← order]
              exact List.mem_flatMap.mpr ⟨none, member, by simp [ListPage.rowEvents]⟩
            exact (noNullEvent wire absent).elim

public theorem readGroup_wire {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup checked ordinal = .ok rows) : GroupWire checked ordinal rows := by
  unfold readGroup at h
  cases selected : checked.frameGroup ordinal with
  | error err => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · rename_i frame single
      cases decoded : readFrame checked framed frame with
      | error err => simp [decoded] at h
      | ok output =>
        obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
        exact ⟨framed, frame, ListFile.frameGroup_wire selected, single, readFrame_wire decoded⟩
    · contradiction

private theorem denote_prefix {checked : Checked} {before after : List Nat} {groups : List (List Row)}
    (h : before.mapM (readGroup checked) = .ok groups) :
    Reader.denoteGroups (readAt checked) (before ++ after) =
      let suffix := Reader.denoteGroups (readAt checked) after
      (groups.map (rowsOf checked) ++ suffix.1, suffix.2) := by
  induction before generalizing groups with
  | nil => cases h; rfl
  | cons ordinal rest ih =>
    cases decoded : readGroup checked ordinal with
    | error err => simp [List.mapM_cons, decoded, Bind.bind, Except.bind] at h
    | ok rows =>
      cases reads : rest.mapM (readGroup checked) with
      | error err => simp [List.mapM_cons, decoded, reads, Bind.bind, Except.bind] at h
      | ok earlier =>
        simp [List.mapM_cons, decoded, reads, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        subst groups
        simp [Reader.denoteGroups, readAt, decoded, Except.map, Except.mapError, ih reads]

public theorem convert_first_error {limits : Limits} {source : Bytes} {checked : Checked}
    {before after : List Nat} {ordinal : Nat} {groups : List (List Row)} {cause : GroupError}
    (opened : openFile limits.parquet source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : before.mapM (readGroup checked) = .ok groups)
    (failed : readGroup checked ordinal = .error cause) :
    (convert limits source).trace = .ok ⟨schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ rowsOf checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) := by
  simp [convert, opened, split, denote_prefix earlier, Reader.denoteGroups, readAt, failed, writeBatches,
    Except.map, Except.mapError, List.map_map]

private theorem completed {checked : Checked} {indices : List Nat}
    (ended : (Reader.denoteGroups (readAt checked) indices).2 = .eos) :
    ∃ groups, indices.mapM (readGroup checked) = .ok groups ∧
      List.Forall₂ (GroupWire checked) indices groups ∧
      (Reader.denoteGroups (readAt checked) indices).1 = groups.map (rowsOf checked) := by
  induction indices with
  | nil => exact ⟨[], rfl, .nil, rfl⟩
  | cons ordinal rest ih =>
    rw [Reader.denoteGroups] at ended
    cases decoded : readGroup checked ordinal with
    | error err => simp [readAt, decoded, Except.map, Except.mapError] at ended
    | ok rows =>
      have tail : (Reader.denoteGroups (readAt checked) rest).2 = .eos := by
        simpa [readAt, decoded, Except.map, Except.mapError] using ended
      obtain ⟨groups, reads, original, ordered⟩ := ih tail
      refine ⟨rows :: groups, ?_, .cons (readGroup_wire decoded) original, ?_⟩
      · simp [List.mapM_cons, decoded, reads, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp [Reader.denoteGroups, readAt, decoded, Except.map, Except.mapError, ordered]

private theorem rows_project (checked : Checked) (groups : List (List Row)) :
    (groups.map fun rows => (AlignedColumns.ofRows (rowsOf checked rows)).values (0 : Fin 1)) = groups := by
  simp [List.map_map, Function.comp_def, AlignedColumns.ofRows, rowsOf]

public theorem convert_readback {limits : Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire := by
  cases opened : openFile limits.parquet source with
  | error err => simp [convert, opened] at h
  | ok checked =>
    let reference := Reader.denoteGroups (readAt checked) (List.range checked.snapshot.groupCount)
    simp only [convert, opened] at h
    change writeBatches limits.ipc checked (reference.1.map AlignedColumns.ofRows) reference.2 = .ok wire at h
    have ended : reference.2 = .eos := by
      cases result : reference.2 <;> simp_all [writeBatches]
    obtain ⟨groups, reads, original, ordered⟩ := completed ended
    have trace : (convert limits source).trace = .ok ⟨schema checked,
        ⟨groups.map (AlignedColumns.ofRows ∘ rowsOf checked), .eos⟩⟩ := by
      simp only [convert, opened]
      change (Except.ok ⟨schema checked, ⟨reference.1.map AlignedColumns.ofRows, reference.2⟩⟩ :
        Arrow.Events.EventStream String Cell SourceError) = _
      rw [ended, ordered, List.map_map]
    rw [ended, ordered] at h
    unfold writeBatches at h
    simp only [List.map_map] at h
    change (Arrow.ListInt32.Stream.Writer.emitFor false limits.ipc (fieldOf checked)
      (groups.map fun rows => (AlignedColumns.ofRows (rowsOf checked rows)).values (0 : Fin 1))).mapError
        Error.writer = .ok wire at h
    rw [rows_project] at h
    have written : Arrow.ListInt32.Stream.Writer.emitFor false limits.ipc (fieldOf checked) groups = .ok wire := by
      cases emitted : Arrow.ListInt32.Stream.Writer.emitFor false limits.ipc (fieldOf checked) groups <;>
        simp_all [Except.mapError]
    obtain ⟨decoded, size, native, agrees, wf, envelope, descriptor, batches, parents⟩ :=
      Arrow.ListInt32.Stream.Writer.emitFor_readback written
    exact ⟨checked, groups, decoded, size, opened, ListFile.openFileFor_wire opened,
      reads, original, trace, native, agrees, wf, envelope, descriptor, batches, parents⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer
