module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi
open Silmaril.Relational
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
open ListPage (Row)

private theorem framedPlain_wire {checked : ListFile.Checked} {ordinal : Nat}
    {framed : ListFile.FramedGroup}
    (origin : ListFile.ChunkFrameWire checked ordinal framed 1)
    (absent : framed.chunk.metadata.dictionaryPageOffset = none) :
    ListFile.FramedGroupWire checked ordinal framed 1 :=
  ⟨origin.group, origin.chunk, origin.path, origin.physical, origin.codec, absent,
    origin.indexPageOffset, origin.span, origin.frames, origin.chain⟩

private theorem readDictionaryGroup_wire {limits : Snappy.DictionaryV1.Limits}
    {walk : Snappy.DictionaryV1.DataWalk} {witness : Snappy.DictionaryV1.WalkWitness}
    {checked : ListFile.Checked} {ordinal expanded left : Nat} {framed : ListFile.FramedGroup} {rows : List Row}
    (origin : ListFile.ChunkFrameWire checked ordinal framed 1)
    (sound : ∀ {checked column entries ordinal budget state frames left next},
      walk checked column entries ordinal budget state frames = .ok (left, next) →
      ∃ pages, witness checked column entries frames pages ∧
        pages.flatten.length + left.slots = budget.slots ∧
        Snappy.expandedSize frames + left.expanded = budget.expanded ∧ state.feed pages.flatten = .ok next)
    (h : readDictionaryGroup limits walk checked framed expanded = .ok (rows, left)) :
    Snappy.DictionaryV1.GroupWireWith limits witness checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  unfold readDictionaryGroup at h
  cases selected : Snappy.DictionaryV1.selectFramedChunk framed with
  | error e => simp [selected, Bind.bind, Except.bind] at h
  | ok chunk =>
    simp only [selected, Bind.bind, Except.bind] at h
    exact Snappy.DictionaryV1.readSelectedGroupWith_wire
      (Snappy.DictionaryV1.selectFramedChunk_wire origin selected).1 sound h

public theorem readFramedGroup_wire {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {framed : ListFile.FramedGroup} {rows : List Row}
    (origin : ListFile.ChunkFrameWire checked ordinal framed 1)
    (h : readFramedGroup limits checked framed expanded = .ok (rows, left)) :
    ProfileWire limits checked ordinal rows (expanded - left) (classify framed.frames) ∧ left ≤ expanded := by
  unfold readFramedGroup at h
  cases classified : classify framed.frames with
  | plain =>
    simp only [classified] at h
    cases offset : framed.chunk.metadata.dictionaryPageOffset with
    | some n => simp [offset] at h
    | none =>
      simp only [offset, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
      cases decoded : Snappy.readFramedGroupFor .v2 limits.snappy checked framed expanded with
      | error cause => simp [decoded, Except.mapError] at h
      | ok result =>
        obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
        exact Snappy.readFramedGroupFor_wire (framedPlain_wire origin offset) decoded
  | dictionary =>
    simp only [classified] at h
    cases decoded : readDictionaryGroup limits (dictionaryWalk limits) checked framed expanded with
    | error cause => simp [decoded, Except.mapError] at h
    | ok result =>
      obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
      obtain ⟨wire, bound⟩ := readDictionaryGroup_wire (walk := dictionaryWalk limits)
        (witness := fun group _ entries => List.Forall₂ (Snappy.DictionaryV2.FrameWire limits group entries))
        origin (fun read => by
          obtain ⟨pages, matching, slots, bytes, fed, _⟩ :=
            Snappy.DictionaryV1.readFramesUsing_wire (fun proof => Snappy.DictionaryV2.readFrame_wire proof) read
          exact ⟨pages, matching, slots, bytes, fed⟩) decoded
      exact ⟨⟨wire⟩, bound⟩
  | fallback =>
    simp only [classified] at h
    cases decoded : readDictionaryGroup limits (Snappy.DictionaryFallbackV2.walk limits) checked framed expanded with
    | error cause => simp [decoded, Except.mapError] at h
    | ok result =>
      obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
      exact readDictionaryGroup_wire (walk := Snappy.DictionaryFallbackV2.walk limits)
        (witness := fun group _ => Snappy.DictionaryFallbackV2.FramesWire limits group)
        origin (fun read => Snappy.DictionaryFallbackV2.readFrames_wire read) decoded

public theorem readGroup_wire {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded := by
  unfold Snappy.DispatchV2.readGroup at h
  cases framed : checked.frameGroupWith 1 true ordinal with
  | error cause => simp [framed, Except.mapError, Bind.bind, Except.bind] at h
  | ok group =>
    simp only [framed, Except.mapError, Bind.bind, Except.bind] at h
    have origin := (ListFile.frameGroupWith_wire framed).1
    obtain ⟨wire, budget⟩ := readFramedGroup_wire origin h
    exact ⟨⟨group, origin, wire⟩, budget⟩

public theorem convert_first_error {limits : Snappy.DictionaryV1.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : Snappy.DispatchV2.GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : Snappy.readGroupsWith SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Snappy.convertWith_first_error (errors := errors) opened split earlier failed

public theorem convert_readback {limits : Snappy.DictionaryV1.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Snappy.convertWith_readback (errors := errors)
    (read := readGroup limits) (witness := GroupWire limits) (fun proof => readGroup_wire proof) h

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DispatchV2
