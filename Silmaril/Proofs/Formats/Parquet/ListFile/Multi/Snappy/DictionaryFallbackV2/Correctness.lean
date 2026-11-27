module

public import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV2.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.Multi
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy (Budget expandedSize)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryV1 (readFramesUsing)
open Silmaril.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2
open Silmaril.Relational
open ListPage (Event State Row)


private theorem readPlainFrame_wire {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} {events : List Event}
    (h : readPlainFrame limits checked budget frame = .ok events) :
    Snappy.V2FrameWire limits.snappy checked frame events ∧
      events.length ≤ budget.slots ∧ frame.value.uncompressedSize ≤ budget.expanded := by
  unfold readPlainFrame at h
  split at h
  · contradiction
  cases read : Snappy.readV2Frame limits.snappy checked budget frame with
  | error cause => simp [read, Except.mapError] at h
  | ok result =>
    obtain rfl := Except.ok.inj (by simpa only [read, Except.mapError] using h)
    exact Snappy.readV2Frame_wire read

public theorem readFrames_wire {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget left : Budget} {state next : State} {frames : List Page.Frame}
    (h : readFrames limits checked entries ordinal budget state frames = .ok (left, next)) :
    ∃ pages, FramesWire limits checked entries frames pages ∧
      pages.flatten.length + left.slots = budget.slots ∧
      expandedSize frames + left.expanded = budget.expanded ∧ state.feed pages.flatten = .ok next := by
  cases frames with
  | nil => contradiction
  | cons first rest =>
    let frames := first :: rest
    let indexedFrames := frames.takeWhile isDictionaryData
    let suffix := frames.dropWhile isDictionaryData
    change (if indexedFrames.isEmpty then _ else _) = _ at h
    split at h
    · contradiction
    rename_i nonemptyPrefix
    change ((do
      let (remaining, advanced) ← readFramesUsing (Snappy.DictionaryV2.readFrame limits checked entries)
        ordinal budget state indexedFrames
      if suffix.isEmpty then throw .missingPlainSuffix
      else readFramesUsing (readPlainFrame limits checked) (ordinal + indexedFrames.length) remaining advanced suffix) : Except Snappy.DictionaryV1.GroupError (Budget × State)) = _ at h
    cases decoded : readFramesUsing (Snappy.DictionaryV2.readFrame limits checked entries) ordinal budget state indexedFrames with
    | error cause => simp [decoded, Bind.bind, Except.bind] at h
    | ok output =>
      obtain ⟨between, middle⟩ := output
      simp only [decoded, Bind.bind, Except.bind] at h
      split at h
      · contradiction
      rename_i nonemptySuffix
      have combined : indexedFrames ++ suffix = frames := List.takeWhile_append_dropWhile
      obtain ⟨indexed, iw, islots, ibytes, ifeed, _⟩ :=
        Snappy.DictionaryV1.readFramesUsing_wire (fun proof => Snappy.DictionaryV2.readFrame_wire proof) decoded
      obtain ⟨plain, pw, pslots, pbytes, pfeed, _⟩ :=
        Snappy.DictionaryV1.readFramesUsing_wire (fun proof => readPlainFrame_wire proof) h
      refine ⟨indexed ++ plain, ⟨indexedFrames, suffix, indexed, plain, ?_, ?_, combined.symm, rfl, iw, pw⟩,
        ?_, ?_, ?_⟩
      · simpa using nonemptyPrefix
      · simpa using nonemptySuffix
      · simp only [List.flatten_append, List.length_append]
        omega
      · change expandedSize frames + left.expanded = budget.expanded
        rw [← combined]
        simp only [expandedSize, List.map_append, List.sum_append] at ibytes pbytes ⊢
        omega
      · rw [List.flatten_append, ListPage.feed_append, ifeed]
        exact pfeed

public theorem readGroup_wire {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked} {ordinal expanded left : Nat}
    {rows : List Row} (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    GroupWire limits checked ordinal rows (expanded - left) ∧ left ≤ expanded :=
  Snappy.DictionaryV1.readGroupWith_wire (walk := walk limits) (witness := fun checked _ => FramesWire limits checked)
    (fun proof => readFrames_wire proof) h

private def PageCounts (frame : Page.Frame) (events : List Event) : Prop :=
  ∃ info, frame.value.kind = .dataV2 info ∧
    info.numValues = events.length ∧ info.numRows = Snappy.pageRows events ∧
    info.numNulls = Snappy.pageNulls events

private theorem indexedCounts {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {entries : Array Int32} {frame : Page.Frame} {events : List Event}
    (h : Snappy.DictionaryV2.FrameWire limits checked entries frame events) : PageCounts frame events := by
  obtain ⟨_, _, info, _, _, _, _, _, _, kind, _, _, _, _, _, sections, _, rows, nulls, _⟩ := h.data
  exact ⟨info, kind, sections.slotCount.symm, rows.symm, nulls.symm⟩

private theorem plainCounts {limits : Snappy.Limits} {checked : ListFile.Checked}
    {frame : Page.Frame} {events : List Event}
    (h : Snappy.V2FrameWire limits checked frame events) : PageCounts frame events := by
  obtain ⟨_, _, info, _, _, _, _, _, kind, _, _, sections, _, rows, nulls, _⟩ := h.data
  exact ⟨info, kind, sections.slotCount.symm, rows.symm, nulls.symm⟩

private theorem headerTotals {frames : List Page.Frame} {pages : List (List Event)}
    (h : List.Forall₂ PageCounts frames pages) :
    ∃ infos,
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) frames infos ∧
      (infos.map (·.numValues)).sum = pages.flatten.length ∧
      (infos.map (·.numRows)).sum = Snappy.pageRows pages.flatten ∧
      (infos.map (·.numNulls)).sum = Snappy.pageNulls pages.flatten := by
  induction h with
  | nil => exact ⟨[], .nil, rfl, rfl, rfl⟩
  | cons single _ ih =>
    obtain ⟨info, kind, count, rows, nulls⟩ := single
    obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := ih
    refine ⟨info :: infos, .cons kind all, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, valueTotal, count]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, rowTotal, rows, Snappy.pageRows, List.countP_append]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, nullTotal, nulls, Snappy.pageNulls, List.countP_append]

public theorem readGroup_counts {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {ordinal expanded left : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal expanded = .ok (rows, left)) :
    ∃ chunk infos, Snappy.DictionaryV1.ChunkWire checked ordinal chunk ∧
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info)
        (chunk.firstData :: chunk.rest) infos ∧
      (infos.map (·.numValues)).sum = chunk.framed.chunk.metadata.numValues.toNat ∧
      (infos.map (·.numRows)).sum = chunk.framed.group.numRows.toNat ∧
      (infos.map (·.numNulls)).sum = Snappy.pageNulls (rows.flatMap ListPage.rowEvents) := by
  obtain ⟨chunk, _, pages, original, _, phase, slots, rowCount, _, events, _⟩ := (readGroup_wire h).1
  obtain ⟨_, _, _, _, _, _, frameOrder, pageOrder, indexed, plain⟩ := phase.data
  have counts : List.Forall₂ PageCounts (chunk.firstData :: chunk.rest) pages := by
    rw [frameOrder, pageOrder]
    exact List.rel_append (indexed.imp (fun _ _ => indexedCounts)) (plain.imp (fun _ _ => plainCounts))
  obtain ⟨infos, all, valueTotal, rowTotal, nullTotal⟩ := headerTotals counts
  rw [← events, Snappy.pageRows_of_rows, rowCount] at rowTotal
  exact ⟨chunk, infos, original, all, valueTotal.trans slots, rowTotal, by simpa [events] using nullTotal⟩

public theorem readFrames_prefix_error {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget : Budget} {state : State} {frames : List Page.Frame} {cause : Snappy.DictionaryV1.GroupError}
    (nonempty : frames.takeWhile isDictionaryData ≠ [])
    (failed : readFramesUsing (Snappy.DictionaryV2.readFrame limits checked entries) ordinal budget state
      (frames.takeWhile isDictionaryData) = .error cause) :
    readFrames limits checked entries ordinal budget state frames = .error cause := by
  cases frames with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => simp [Snappy.DictionaryFallbackV2.readFrames, nonempty, failed, Bind.bind, Except.bind]

public theorem readFrames_suffix_error {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked} {entries : Array Int32}
    {ordinal : Nat} {budget left : Budget} {state next : State}
    {frames earlier rest : List Page.Frame} {frame : Page.Frame} {cause : Snappy.DictionaryV1.FrameError}
    (nonempty : frames.takeWhile isDictionaryData ≠ [])
    (decodedPrefix : readFramesUsing (Snappy.DictionaryV2.readFrame limits checked entries) ordinal budget state
      (frames.takeWhile isDictionaryData) = .ok (left, next))
    (split : frames.dropWhile isDictionaryData = earlier ++ frame :: rest)
    {remaining : Budget} {advanced : State}
    (before : readFramesUsing (readPlainFrame limits checked) (ordinal + (frames.takeWhile isDictionaryData).length)
      left next earlier = .ok (remaining, advanced))
    (failed : readPlainFrame limits checked remaining frame = .error cause) :
    readFrames limits checked entries ordinal budget state frames =
      .error (.frame (ordinal + (frames.takeWhile isDictionaryData).length + earlier.length) frame.header.start cause) := by
  cases frames with
  | nil => exact False.elim (nonempty rfl)
  | cons first restFrames =>
    have suffix : ((first :: restFrames).dropWhile isDictionaryData).isEmpty = false := by
      rw [split]
      simp
    unfold Snappy.DictionaryFallbackV2.readFrames
    simp only [List.isEmpty_eq_false_iff.mpr nonempty, Bool.false_eq_true, ↓reduceIte, decodedPrefix,
      Bind.bind, Except.bind, suffix]
    rw [split, Snappy.DictionaryV1.readFramesUsing_append before]
    exact Snappy.DictionaryV1.readFramesUsing_read_error failed

public theorem readPlainFrame_reentry {limits : Snappy.DictionaryV1.Limits} {checked : ListFile.Checked}
    {budget : Budget} {frame : Page.Frame} (kind : isDictionaryData frame = true) :
    readPlainFrame limits checked budget frame = .error .dictionaryReentry := by
  simp [readPlainFrame, kind]

public theorem convert_first_error {limits : Snappy.DictionaryV1.Limits} {source : Bytes} {checked : ListFile.Checked}
    {before after : List Nat} {ordinal left : Nat} {groups : List (List Row)} {cause : Snappy.DictionaryV1.GroupError}
    (opened : ListFile.openFile limits.snappy.parquet.file source = .ok checked)
    (split : List.range checked.snapshot.groupCount = before ++ ordinal :: after)
    (earlier : Snappy.readGroupsWith Snappy.DictionaryV1.SourceError.groupFailure
      (readGroup limits) checked limits.snappy.maxExpandedBytes before = (groups, .ok left))
    (failed : readGroup limits checked ordinal left = .error cause) :
    (convert limits source).trace = .ok ⟨ListFile.schema checked,
      ⟨groups.map (AlignedColumns.ofRows ∘ ListFile.rows checked), .readError (.groupFailure ordinal cause)⟩⟩ ∧
    (convert limits source).wire = .error (.source (.groupFailure ordinal cause)) :=
  Snappy.convertWith_first_error (errors := Snappy.DictionaryV1.errors) opened split earlier failed

public theorem convert_readback {limits : Snappy.DictionaryV1.Limits} {source : Bytes} {wire : KBytes}
    (h : (convert limits source).wire = .ok wire) : Readback limits source wire :=
  Snappy.convertWith_readback (errors := Snappy.DictionaryV1.errors)
    (read := readGroup limits) (witness := GroupWire limits) (fun proof => readGroup_wire proof) h

end Silmaril.Proofs.Formats.Parquet.ListFile.Multi.Snappy.DictionaryFallbackV2
