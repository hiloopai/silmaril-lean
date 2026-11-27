module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Defs
import Silmaril.Formats.Parquet.ListFile.Multi.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer (Checked SectionsWire)
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy
open ListPage (Event Row)

private theorem checkedExtent {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status} (h : Page.Checksum.verify cap source frame = .ok status) :
    frame.value.compressedSize ≤ cap ∧ Page.Checksum.PayloadWithin source frame := by
  cases status with
  | absent =>
    obtain ⟨cap, extent, _⟩ := Page.Checksum.verify_absent_iff.mp h
    exact ⟨cap, extent⟩
  | valid declared =>
    obtain ⟨cap, extent, _, _⟩ := Page.Checksum.verify_valid_iff.mp h
    exact ⟨cap, extent⟩

public theorem readSections_wire {limits : Limits} {checked : Checked} {frame : Page.Frame}
    {info : Page.DataV2} {sections : ListFile.Multi.Snappy.V2Sections}
    (kind : frame.value.kind = .dataV2 info)
    (h : readSections limits checked frame info = .ok sections) : StoredWire limits checked frame info sections := by
  unfold readSections at h
  dsimp only at h
  cases verified : Page.Checksum.verify limits.maxStoredPageBytes checked.snapshot.bytes frame with
  | error cause => simp [verified, Except.mapError, Bind.bind, Except.bind] at h
  | ok status =>
    simp only [verified, Except.mapError, Bind.bind, Except.bind] at h
    obtain ⟨cap, extent⟩ := checkedExtent verified
    obtain ⟨slice, size⟩ := Page.Checksum.payload_exact extent
    have body := ListFile.Multi.Snappy.prepareV2_wire h
    obtain ⟨suffix, _, ordered, _, _, _, _, _⟩ := body.exact
    have fits := congrArg List.length ordered
    simp only [List.length_append, Bytes.length_toList, size, body.repetitionSize, body.definitionSize] at fits
    have width := extent.2.2.1
    let defs := frame.payload.start + info.repetitionBytes
    let scalars := defs + info.definitionBytes
    let spans : Page.V2Spans :=
      ⟨⟨frame.payload.start, defs⟩, ⟨defs, scalars⟩, ⟨scalars, frame.payload.stop⟩⟩
    have geometry : frame.payload.start + info.repetitionBytes + info.definitionBytes ≤ frame.payload.stop := by
      omega
    refine ⟨status, Page.Checksum.payloadBytes checked.snapshot.bytes frame, spans, verified, slice,
      size, size ▸ cap, ?_, ?_, ?_, ?_, body⟩
    · simp [Page.Frame.v2Spans, kind, geometry, spans, defs, scalars]
    · simp [spans, defs, body.repetitionSize]
    · simp [spans, scalars, body.definitionSize]
    · simp only [spans, scalars, defs, ListFile.Multi.Snappy.v2LevelBytes]
      omega

public theorem suffix_wire {checked : Checked} {frame : Page.Frame} {info : Page.DataV2}
    {stored : Bytes} {sections : ListFile.Multi.Snappy.V2Sections}
    (wire : ListFile.Multi.Snappy.V2BodyWire checked frame info stored sections) :
    ∃ suffix,
      stored.toList = sections.repetition.toList ++ sections.definition.toList ++ suffix ∧
      suffix.length = frame.value.compressedSize - ListFile.Multi.Snappy.v2LevelBytes info ∧
      sections.scalars.length = frame.value.uncompressedSize - ListFile.Multi.Snappy.v2LevelBytes info ∧
      (if info.isCompressed then
        Payload.Decodes (frame.value.uncompressedSize - ListFile.Multi.Snappy.v2LevelBytes info)
          .snappy suffix sections.scalars.toList
      else suffix = sections.scalars.toList) := by
  obtain ⟨suffix, codec, order, storedSize, expandedSize, _, selected, decoded⟩ := wire.exact
  refine ⟨suffix, order, storedSize, expandedSize, ?_⟩
  cases flag : info.isCompressed with
  | false =>
    simp [ListFile.Multi.Snappy.v2Codec, flag, Payload.Codec.ofId] at selected
    subst codec
    cases decoded
    rfl
  | true =>
    simp [ListFile.Multi.Snappy.v2Codec, flag, Payload.Codec.ofId] at selected
    subst codec
    exact decoded

public theorem readEvents_wire {limits : Limits} {checked : Checked} {frame : Page.Frame}
    {info : Page.DataV2} {events : List Event} (kind : frame.value.kind = .dataV2 info)
    (h : readEvents limits checked frame info = .ok events) : EventsWire limits checked frame info events := by
  unfold readEvents at h
  simp only [Bind.bind, Except.bind] at h
  cases prepared : readSections limits checked frame info with
  | error cause => simp [prepared] at h
  | ok sections =>
    simp only [prepared] at h
    cases decoded : ListFile.RequiredContainer.decodeSections checked.limits.page info.numValues
        sections.repetition sections.definition sections.scalars with
    | error cause => simp [decoded, Except.mapError] at h
    | ok output =>
      simp only [decoded, Except.mapError] at h
      cases counted : ListFile.Multi.Snappy.checkV2Counts info output with
      | error cause => simp [counted] at h
      | ok accepted =>
        cases accepted
        simp only [counted] at h
        obtain rfl := Except.ok.inj h
        obtain ⟨boundary, rows, absent⟩ := ListFile.Multi.Snappy.checkV2Counts_wire counted
        exact ⟨sections, readSections_wire kind prepared, ListFile.RequiredContainer.decodeSections_wire decoded,
          boundary, rows, absent⟩

public theorem readFrame_wire {limits : Limits} {checked : Checked} {framed : ListFile.FramedGroup}
    {frame : Page.Frame} {rows : List Row}
    (h : readFrame limits checked framed frame = .ok rows) : FrameWire limits checked framed frame rows := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i codec
    split at h
    · contradiction
    rename_i encoding
    split at h
    · contradiction
    rename_i slots
    dsimp only at h
    split at h
    · contradiction
    rename_i rowCaps
    push Not at rowCaps
    simp only [Except.mapError, Bind.bind, Except.bind] at h
    cases decoded : readEvents limits checked frame info with
    | error cause => simp [decoded] at h
    | ok events =>
      simp only [decoded] at h
      cases assembled : ListPage.reconstruct events with
      | error cause => simp [assembled] at h
      | ok output =>
        simp only [assembled] at h
        split at h
        · contradiction
        rename_i groupRows
        obtain rfl := Except.ok.inj h
        have groupCount := not_not.mp groupRows
        obtain ⟨sections, prepared, sectionWire, boundary, rowCount, nulls⟩ := (readEvents_wire kind decoded).data
        have ordered := ListPage.reconstruct_wire assembled
        have sourceRows : output.length = info.numRows := by
          rw [← ListFile.Multi.Snappy.pageRows_of_rows output, ordered]
          exact rowCount
        have ⟨physical, extent⟩ := ListFile.RequiredContainer.V2.sections_physical sectionWire
        refine ⟨ListFile.RequiredContainer.reconstruct_present sectionWire assembled, info, sections, kind,
          not_not.mp codec, not_not.mp encoding, prepared, ordered ▸ sectionWire,
          ordered ▸ boundary, not_not.mp slots, rowCaps.2, sourceRows, groupCount, groupCount ▸ rowCaps.1,
          ordered ▸ nulls, ?_, ?_⟩
        · rwa [← nulls]
        · rw [ordered, ← nulls]
          exact physical
  · contradiction

public theorem frame_counts {limits : Limits} {checked : Checked} {framed : ListFile.FramedGroup}
    {frame : Page.Frame} {rows : List Row} (wire : FrameWire limits checked framed frame rows) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire limits checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls := by
  obtain ⟨info, sections, kind, _, _, stored, raw, _, _, _, rows, _, _, nulls, _, _⟩ := wire.data
  obtain ⟨reps, defs, counts⟩ := ListFile.RequiredContainer.V2.sections_counts raw rows nulls
  exact ⟨info, sections, reps, defs, kind, stored, counts⟩

public theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal = .ok rows) : GroupWire limits checked ordinal rows := by
  unfold readGroup ListFile.RequiredContainer.readGroupWith at h
  cases selected : checked.frameGroupFor 1 ordinal with
  | error cause => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · rename_i frame singleton
      cases decoded : readFrame limits checked framed frame with
      | error cause => simp [decoded] at h
      | ok output =>
        obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
        exact ⟨framed, frame, ListFile.frameGroupFor_wire selected, singleton, readFrame_wire decoded⟩
    · contradiction

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy
