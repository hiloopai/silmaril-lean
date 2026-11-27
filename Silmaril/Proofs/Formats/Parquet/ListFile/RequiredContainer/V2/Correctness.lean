module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Defs
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Plain.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2
open Silmaril.Formats.Parquet.ListFile.RequiredContainer (Checked Limits SectionsWire SectionsWireUsing Triple eventWire valueMask)
open Silmaril.Relational
open ListPage (Event Row)

public theorem readSections_wire {limits : ListPage.Limits} {source : Bytes} {frame : Page.Frame}
    {info : Page.DataV2} {sections : Sections} (kind : frame.value.kind = .dataV2 info)
    (h : readSections limits source frame info = .ok sections) : RawWire limits source frame info sections := by
  unfold readSections at h
  dsimp only at h
  split at h
  · contradiction
  rename_i sizes
  push Not at sizes
  split at h
  · contradiction
  rename_i cap
  split at h
  · contradiction
  rename_i levelFit
  split at h
  · contradiction
  rename_i limitsFit
  cases sliced : source.slice? frame.payload.start (some frame.payload.stop) with
  | none => simp [sliced] at h
  | some body =>
    simp only [sliced] at h
    obtain rfl := Except.ok.inj h
    have bodySize := Bytes.length_of_slice? sliced
    simp only [Option.getD_some, sizes.2, Nat.add_sub_cancel_left] at bodySize
    have levels : info.repetitionBytes + info.definitionBytes ≤ frame.value.compressedSize :=
      Nat.le_of_not_gt levelFit
    let defs := frame.payload.start + info.repetitionBytes
    let values := defs + info.definitionBytes
    let spans : Page.V2Spans :=
      ⟨⟨frame.payload.start, defs⟩, ⟨defs, values⟩, ⟨values, frame.payload.stop⟩⟩
    have geometry : values ≤ frame.payload.stop := by dsimp [values, defs]; omega
    have repSize : (body.toList.take info.repetitionBytes).length = info.repetitionBytes := by
      rw [List.length_take, Bytes.length_toList, bodySize, Nat.min_eq_left (by omega)]
    have defSize : ((body.toList.drop info.repetitionBytes).take info.definitionBytes).length =
        info.definitionBytes := by
      rw [List.length_take, List.length_drop, Bytes.length_toList, bodySize, Nat.min_eq_left (by omega)]
    have scalarSize : ((body.toList.drop info.repetitionBytes).drop info.definitionBytes).length =
        frame.value.compressedSize - (info.repetitionBytes + info.definitionBytes) := by
      simp only [List.length_drop, Bytes.length_toList, bodySize]
      omega
    push Not at limitsFit
    refine ⟨sizes.1, Nat.le_of_not_gt cap, limitsFit,
      by simpa only [Bytes.length_ofList] using repSize,
      by simpa only [Bytes.length_ofList] using defSize,
      by simpa only [Bytes.length_ofList] using scalarSize, body, spans, sliced, bodySize, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [values, defs] at geometry
      simp [Page.Frame.v2Spans, kind, geometry, spans, defs, values]
    · simp only [spans, defs, Bytes.length_ofList, repSize, Nat.add_sub_cancel_left]
    · simp only [spans, values, Bytes.length_ofList, defSize, Nat.add_sub_cancel_left]
    · simp only [spans, Bytes.length_ofList, scalarSize]
      dsimp [values, defs]
      omega
    · simp only [Bytes.toList_ofList, List.append_assoc, List.take_append_drop]

private theorem wireValue (event : Event) :
    (eventWire event).bind (fun triple => triple.2.2) = event.wire.2.2 := by
  cases event <;> rfl

private theorem slot_values {events : List Event} {repetitions definitions : List Nat}
    {entries : List (Option Int32)}
    (repSize : repetitions.length = entries.length) (defSize : definitions.length = entries.length)
    (ordered : events.map eventWire = (repetitions.zip (definitions.zip entries)).map some) :
    events.map (fun event => event.wire.2.2) = entries := by
  have mapped := congrArg (List.map (fun triple : Option Triple => triple.bind (fun slot => slot.2.2))) ordered
  rw [List.map_map, List.map_map] at mapped
  change events.map (fun event => (eventWire event).bind (fun triple => triple.2.2)) =
    (repetitions.zip (definitions.zip entries)).map (Prod.snd ∘ Prod.snd) at mapped
  rw [← List.map_map, List.map_snd_zip (by simp [repSize, defSize]),
    List.map_snd_zip (by simp [defSize])] at mapped
  simpa only [wireValue] using mapped

private theorem slot_count {entries : List (Option Int32)} :
    entries.countP Option.isSome + entries.countP Option.isNone = entries.length := by
  have complement : (fun (item : Option Int32) => decide (¬item.isSome = true)) = Option.isNone := by
    funext item
    cases item <;> rfl
  have count := List.length_eq_countP_add_countP Option.isSome (l := entries)
  rw [complement] at count
  exact count.symm

private theorem words_size (words : List (List UInt8))
    (widths : ∀ word ∈ words, word.length = 4) :
    (words.map List.length).sum = words.length * 4 := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    have first := widths word (by simp)
    have tail : ∀ item ∈ rest, item.length = 4 := fun item member => widths item (by simp [member])
    simp only [List.map_cons, List.sum_cons, first, List.length_cons, ih tail]
    omega

public theorem sections_values {ε : Type} {readValues : Nat → Bytes → Except ε (List Int32)}
    {slots : Nat} {repetition definition scalars : Bytes} {events : List Event}
    (wire : SectionsWireUsing readValues slots repetition definition scalars events) :
    readValues (slots - missingSlots events) scalars = .ok (events.filterMap (fun event => event.wire.2.2)) := by
  obtain ⟨reps, defs, values, entries, _, _, repCount, defCount, entryCount, read, mask, valuesOrder, eventOrder⟩ := wire.data
  have order := slot_values (repCount.trans entryCount.symm) (defCount.trans entryCount.symm) eventOrder
  have missing : missingSlots events = entries.countP Option.isNone := by
    rw [← order, List.countP_map]
    rfl
  have present : (valueMask defs).count true = entries.countP Option.isSome := by
    rw [← mask, List.count, List.countP_map]
    simp [Function.comp_def]
  have count : slots - missingSlots events = (valueMask defs).count true := by
    rw [missing, present, ← entryCount, ← slot_count]
    omega
  have physical : events.filterMap (fun event => event.wire.2.2) = values := by
    rw [← valuesOrder, ← order, List.filterMap_map]
    rfl
  rw [count, physical]
  exact read

public theorem sections_physical {slots : Nat} {repetition definition scalars : Bytes} {events : List Event}
    (wire : SectionsWire slots repetition definition scalars events) :
    Plain.decodeInt32 (slots - missingSlots events) scalars = .ok (events.filterMap (fun event => event.wire.2.2)) ∧
    scalars.length = 4 * (slots - missingSlots events) := by
  have read := sections_values wire.usingPlain
  refine ⟨read, ?_⟩
  obtain ⟨_, words, wordBytes, wordCount, widths, _⟩ := Plain.decodeFixedWidth_ok_iff.mp read
  rw [← Bytes.length_toList, wordBytes, List.length_flatten, words_size words widths, wordCount]
  omega

public theorem readFrame_wire {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (h : readFrame checked framed frame = .ok rows) : FrameWire checked framed frame rows := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i codec
    split at h
    · contradiction
    rename_i crc
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
    simp only [Bind.bind, Except.bind] at h
    cases raw : readSections checked.limits.page checked.snapshot.bytes frame info with
    | error error => simp [raw] at h
    | ok sections =>
      simp only [raw, Except.mapError] at h
      cases decoded : ListFile.RequiredContainer.decodeSections checked.limits.page info.numValues
          sections.repetition sections.definition sections.scalars with
      | error error => simp [decoded] at h
      | ok events =>
        simp only [decoded] at h
        split at h
        · contradiction
        rename_i missing
        cases assembled : ListPage.reconstruct events with
        | error error => simp [assembled] at h
        | ok output =>
          simp only [assembled] at h
          split at h
          · contradiction
          rename_i decodedRows
          split at h
          · contradiction
          rename_i groupRows
          obtain rfl := Except.ok.inj h
          have noCrc : frame.value.crc = none := by cases present : frame.value.crc <;> simp_all
          have physical := ListFile.RequiredContainer.decodeSections_wire decoded
          have ordered := ListPage.reconstruct_wire assembled
          have ⟨read, extent⟩ := sections_physical physical
          refine ⟨ListFile.RequiredContainer.reconstruct_present physical assembled, info, sections, kind,
            not_not.mp codec, noCrc, not_not.mp encoding, readSections_wire kind raw, ordered ▸ physical,
            not_not.mp slots, not_not.mp decodedRows, rowCaps.2, not_not.mp groupRows,
            ?_, ?_, ?_⟩
          · rw [ordered]; exact not_not.mp missing
          · rwa [← not_not.mp missing]
          · rw [ordered, ← not_not.mp missing]; exact read
  · contradiction

private theorem slot_repetitions {events : List Event} {reps defs : List Nat}
    {entries : List (Option Int32)}
    (fits : reps.length ≤ (defs.zip entries).length)
    (ordered : events.map eventWire = (reps.zip (defs.zip entries)).map some) :
    events.map (fun event => event.wire.1) = reps := by
  have same (event : Event) : ((eventWire event).map Prod.fst).getD 0 = event.wire.1 := by
    cases event <;> rfl
  have mapped := congrArg (List.map (fun triple : Option Triple => (triple.map Prod.fst).getD 0)) ordered
  rw [List.map_map, List.map_map] at mapped
  change events.map (fun event => ((eventWire event).map Prod.fst).getD 0) =
    (reps.zip (defs.zip entries)).map Prod.fst at mapped
  simpa only [same, List.map_fst_zip fits] using mapped

public theorem rowStarts_of_rows (rows : List Row) :
    rowStarts (rows.flatMap ListPage.rowEvents) = rows.length := by
  unfold rowStarts
  have one (row : Row) : (ListPage.rowEvents row).countP (fun event => event.wire.1 == 0) = 1 := by
    cases row with
    | none => rfl
    | some items =>
      cases items with
      | nil => rfl
      | cons item tail => simp [ListPage.rowEvents, ListPage.Event.wire, Function.comp_def]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.flatMap_cons, List.countP_append, one, ih, List.length_cons]
    omega

public theorem event_counts_using {ε : Type} {readValues : Nat → Bytes → Except ε (List Int32)}
    {info : Page.DataV2} {repetition definition scalars : Bytes}
    {events : List Event}
    (sectionWire : SectionsWireUsing readValues info.numValues repetition definition scalars events)
    (rowCount : rowStarts events = info.numRows)
    (nullCount : missingSlots events = info.numNulls) :
    ∃ reps defs,
      Hybrid.Wire 1 info.numValues repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls ∧
      events.map (fun event => event.wire.1) = reps := by
  obtain ⟨reps, defs, _, entries, repWire, defWire, repLength, defLength, entryLength, _, mask, _, ordered⟩ :=
    sectionWire.data
  have repetitions := slot_repetitions (by simp [repLength, defLength, entryLength]) ordered
  have values := slot_values (repLength.trans entryLength.symm) (defLength.trans entryLength.symm) ordered
  have noneEq : (fun (item : Option Int32) => !item.isSome) = Option.isNone := by
    funext item
    cases item <;> rfl
  have missing := congrArg (List.countP (!·)) mask
  simp only [valueMask, List.countP_map, Function.comp_def, noneEq] at missing
  refine ⟨reps, defs, repWire, defWire, repLength, defLength, ?_, ?_, repetitions⟩
  · rw [← repetitions, List.count, List.countP_map]
    exact rowCount
  · change defs.countP (fun d => !(d == 2)) = info.numNulls
    rw [← missing, ← values, List.countP_map]
    exact nullCount

public theorem event_counts {info : Page.DataV2} {repetition definition scalars : Bytes}
    {events : List Event}
    (sectionWire : SectionsWire info.numValues repetition definition scalars events)
    (rowCount : rowStarts events = info.numRows)
    (nullCount : missingSlots events = info.numNulls) :
    ∃ reps defs,
      Hybrid.Wire 1 info.numValues repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls ∧
      events.map (fun event => event.wire.1) = reps :=
  event_counts_using sectionWire.usingPlain rowCount nullCount

public theorem sections_counts {info : Page.DataV2} {repetition definition scalars : Bytes}
    {rows : List Row}
    (sectionWire : SectionsWire info.numValues repetition definition scalars (rows.flatMap ListPage.rowEvents))
    (rowCount : rows.length = info.numRows)
    (nullCount : missingSlots (rows.flatMap ListPage.rowEvents) = info.numNulls) :
    ∃ reps defs,
      Hybrid.Wire 1 info.numValues repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls := by
  obtain ⟨reps, defs, repWire, defWire, repLength, defLength, rowTotal, nullTotal, _⟩ :=
    event_counts sectionWire ((rowStarts_of_rows rows).trans rowCount) nullCount
  exact ⟨reps, defs, repWire, defWire, repLength, defLength, rowTotal, nullTotal⟩

public theorem frame_counts {checked : Checked} {framed : ListFile.FramedGroup} {frame : Page.Frame}
    {rows : List Row} (wire : FrameWire checked framed frame rows) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      reps.count 0 = info.numRows ∧ defs.countP (· != 2) = info.numNulls := by
  obtain ⟨info, sections, kind, _, _, _, raw, sectionWire, _, rowCount, _, _, nullCount, _, _⟩ := wire.data
  obtain ⟨reps, defs, facts⟩ := sections_counts sectionWire rowCount nullCount
  exact ⟨info, sections, reps, defs, kind, raw, facts⟩

public theorem readGroup_wire {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup checked ordinal = .ok rows) : GroupWire checked ordinal rows := by
  unfold readGroup ListFile.RequiredContainer.readGroupUsing ListFile.RequiredContainer.readGroupWith at h
  cases selected : checked.frameGroup ordinal with
  | error error => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · rename_i frame singleton
      cases decoded : readFrame checked framed frame with
      | error error => simp [decoded] at h
      | ok output =>
        obtain rfl := Except.ok.inj (by simpa only [decoded, Except.mapError] using h)
        exact ⟨framed, frame, ListFile.frameGroup_wire selected, singleton, readFrame_wire decoded⟩
    · contradiction

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2
