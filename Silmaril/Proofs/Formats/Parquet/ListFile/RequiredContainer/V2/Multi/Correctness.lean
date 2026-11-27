module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Defs
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Thms
import Silmaril.Formats.Parquet.ListFile.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.Thms
import Silmaril.Formats.Parquet.ListPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Silmaril.Formats.Parquet.ListFile.RequiredContainer (Checked eventWire SectionsWireUsing)
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2 (readSections readSections_wire RawWire
  rowStarts missingSlots event_counts sections_physical rowStarts_of_rows)
open Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi
open ListPage (Event Row State)

public theorem readFrame_wire {checked : Checked} {remaining : Nat} {frame : Page.Frame}
    {events : List Event} (h : readFrame checked remaining frame = .ok events) :
    FrameWire checked frame events ∧ events.length ≤ remaining := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i crc
    split at h
    · contradiction
    rename_i encoding
    split at h
    · contradiction
    rename_i slots
    split at h
    · contradiction
    rename_i rowCap
    simp only [Bind.bind, Except.bind] at h
    cases raw : readSections checked.limits.page checked.snapshot.bytes frame info with
    | error cause => simp [raw, Except.mapError] at h
    | ok sections =>
      simp only [raw, Except.mapError] at h
      cases decoded : ListFile.RequiredContainer.decodeSections checked.limits.page info.numValues
          sections.repetition sections.definition sections.scalars with
      | error cause => simp [decoded] at h
      | ok result =>
        simp only [decoded] at h
        split at h
        · contradiction
        rename_i boundary
        split at h
        · contradiction
        rename_i nulls
        split at h
        · contradiction
        rename_i rows
        obtain rfl := Except.ok.inj h
        have noCrc : frame.value.crc = none := by cases present : frame.value.crc <;> simp_all
        have physical := ListFile.RequiredContainer.decodeSections_wire decoded
        exact ⟨⟨⟨info, sections, kind, noCrc, not_not.mp encoding, readSections_wire kind raw, physical,
          physical.count, not_not.mp rows, not_not.mp nulls, Nat.le_of_not_gt rowCap⟩,
          by simpa only [Bool.not_eq_true] using boundary⟩, physical.count ▸ Nat.le_of_not_gt slots⟩
  · contradiction

public theorem frame_levels {checked : Checked} {frame : Page.Frame} {events : List Event}
    (h : FrameWire checked frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ RawWire checked.limits.page checked.snapshot.bytes frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧ sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
      Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
        .ok (events.filterMap (fun event => event.wire.2.2)) := by
  obtain ⟨info, sections, kind, _, _, raw, physical, _, rows, nulls, _⟩ := h.data
  obtain ⟨reps, defs, repWire, defWire, repLength, defLength, rowTotal, nullTotal, ordered⟩ :=
    event_counts physical rows nulls
  obtain ⟨read, extent⟩ := sections_physical physical
  rw [nulls] at read extent
  refine ⟨info, sections, reps, defs, kind, raw, repWire, defWire, repLength, defLength, ?_, rowTotal,
    nullTotal, extent, read⟩
  rw [← ordered]
  cases events with
  | nil => exact Or.inl rfl
  | cons event tail =>
    have boundary := h.boundary
    cases event with
    | nullList => exact Or.inr rfl
    | emptyList => exact Or.inr rfl
    | first item => exact Or.inr rfl
    | next item => contradiction

public theorem countedFrame {ε : Type} {readValues : Nat → Bytes → Except ε (List Int32)}
    {frame : Page.Frame} {info : Page.DataV2} {repetition definition scalars : Bytes} {events : List Event}
    (kind : frame.value.kind = .dataV2 info)
    (physical : SectionsWireUsing readValues info.numValues repetition definition scalars events)
    (rows : rowStarts events = info.numRows) (absent : missingSlots events = info.numNulls) :
    CountedFrame frame events := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ordered⟩ := physical.data
  refine ⟨info, kind, physical.count, rows, absent, fun invalid => ?_⟩
  have noneMember : none ∈ List.map eventWire events := List.mem_map.mpr ⟨Event.nullList, invalid, rfl⟩
  rw [ordered] at noneMember
  simp at noneMember

public theorem frameTotals {frames : List Page.Frame} {pages : List (List Event)}
    (wire : List.Forall₂ CountedFrame frames pages) :
    ∃ infos,
      List.Forall₂ (fun (frame : Page.Frame) (info : Page.DataV2) => frame.value.kind = .dataV2 info) frames infos ∧
      (infos.map (·.numValues)).sum = pages.flatten.length ∧
      (infos.map (·.numRows)).sum = rowStarts pages.flatten ∧
      (infos.map (·.numNulls)).sum = missingSlots pages.flatten ∧ Event.nullList ∉ pages.flatten := by
  induction wire with
  | nil => exact ⟨[], .nil, rfl, rfl, rfl, by simp⟩
  | cons frame rest ih =>
    obtain ⟨info, kind, count, rows, absent, validHead⟩ := frame.data
    obtain ⟨infos, kinds, slotsSum, rowSum, nullSum, validTail⟩ := ih
    refine ⟨info :: infos, .cons kind kinds, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, count, slotsSum]
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, rowSum, ← rows]
      exact (List.countP_append ..).symm
    · simp only [List.map_cons, List.sum_cons, List.flatten_cons, nullSum, ← absent]
      exact (List.countP_append ..).symm
    · simpa only [List.flatten_cons, List.mem_append, not_or] using And.intro validHead validTail

public theorem readGroupWith_wire {frameError : Type} {codec : Int} {maxGroupSlots : Nat}
    {select : Checked → Nat → Except ListFile.ReadError ListFile.FramedGroup}
    {read : Checked → ListFile.Multi.SlotFrameReader frameError} {feedError : ListPage.Error → frameError}
    {checked : Checked} {ordinal : Nat} {rows : List Row} {witness : Page.Frame → List Event → Prop}
    (selectedWire : ∀ {framed}, select checked ordinal = .ok framed →
      ListFile.FramedGroupWire checked ordinal framed codec)
    (sound : ∀ {remaining frame events}, read checked remaining frame = .ok events →
      witness frame events ∧ CountedFrame frame events ∧ events.length ≤ remaining)
    (h : readGroupWith select maxGroupSlots read feedError checked ordinal = .ok rows) :
    GroupWire maxGroupSlots checked ordinal rows codec witness := by
  unfold readGroupWith at h
  cases selected : select checked ordinal with
  | error cause => simp [selected, Except.mapError, Bind.bind, Except.bind] at h
  | ok framed =>
    simp only [selected, Except.mapError, Bind.bind, Except.bind] at h
    split at h
    · contradiction
    rename_i slotCap
    split at h
    · contradiction
    rename_i rowCap
    cases walked : ListFile.Multi.readFramesWith GroupError.frame feedError (read checked)
        framed.frames 0 framed.chunk.metadata.numValues.toNat State.empty with
    | error cause => simp [walked] at h
    | ok result =>
      obtain ⟨left, state⟩ := result
      simp only [walked] at h
      split at h
      · contradiction
      rename_i noSurplus
      push Not at noSurplus
      subst left
      split at h
      · contradiction
      rename_i rowCount
      obtain rfl := Except.ok.inj h
      obtain ⟨pages, frames, count, fed, ordered⟩ :=
        ListFile.Multi.readFramesWith_wire (read := read checked)
          (witness := fun frame events => witness frame events ∧ CountedFrame frame events)
          (fun decoded => let ⟨wire, counts, bound⟩ := sound decoded; ⟨⟨wire, counts⟩, bound⟩) walked
      have order : state.finish.flatMap ListPage.rowEvents = pages.flatten := by
        simpa only [ListPage.finish_empty, List.flatMap_nil, List.nil_append] using ordered
      have counted := List.Forall₂.imp (fun _ _ both => both.2) frames
      have pageWires := List.Forall₂.imp (fun _ _ both => both.1) frames
      obtain ⟨infos, kinds, slots, starts, missing, present⟩ := frameTotals counted
      refine ⟨?_, framed, pages, infos, selectedWire selected, pageWires, kinds, ListPage.reconstruct_of_feed fed, order,
        slots.trans (by simpa using count), ?_, not_not.mp rowCount, ?_,
        Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩
      · intro row member
        cases row with
        | some children => rfl
        | none =>
          have absent : Event.nullList ∈ pages.flatten := by
            rw [← order]
            exact List.mem_flatMap.mpr ⟨none, member, by simp [ListPage.rowEvents]⟩
          exact (present absent).elim
      · rw [starts, ← order, rowStarts_of_rows]
      · rw [missing, order]

public theorem readGroup_wire {maxGroupSlots : Nat} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup maxGroupSlots checked ordinal = .ok rows) : GroupWire maxGroupSlots checked ordinal rows := by
  apply readGroupWith_wire (read := readFrame) (feedError := fun cause => .data (.page cause))
    ListFile.frameGroup_wire ?_ h
  intro remaining frame events decoded
  obtain ⟨wire, bound⟩ := readFrame_wire decoded
  obtain ⟨info, sections, kind, _, _, _, physical, _, rows, absent, _⟩ := wire.data
  exact ⟨wire, countedFrame kind physical.usingPlain rows absent, bound⟩

public theorem readGroupWith_frame_error {frameError : Type} {maxGroupSlots : Nat}
    {select : Checked → Nat → Except ListFile.ReadError ListFile.FramedGroup}
    {checked : Checked} {ordinal : Nat} {read : Checked → ListFile.Multi.SlotFrameReader frameError}
    {feedError : ListPage.Error → frameError}
    {framed : ListFile.FramedGroup} {before after : List Page.Frame} {frame : Page.Frame}
    {remaining : Nat} {state : State} {cause : frameError}
    (selected : select checked ordinal = .ok framed)
    (slots : framed.chunk.metadata.numValues.toNat ≤ maxGroupSlots)
    (rows : framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (order : framed.frames = before ++ frame :: after)
    (earlier : ListFile.Multi.readFramesWith GroupError.frame feedError (read checked)
      before 0 framed.chunk.metadata.numValues.toNat State.empty = .ok (remaining, state))
    (failed : read checked remaining frame = .error cause ∨
      ∃ events error, read checked remaining frame = .ok events ∧
        state.feed events = .error error ∧ cause = feedError error) :
    readGroupWith select maxGroupSlots read feedError checked ordinal =
      .error (.frame before.length frame.header.start cause) := by
  have prefixStep := ListFile.Multi.readFramesWith_append (after := frame :: after) earlier
  unfold readGroupWith
  simp only [selected, Except.mapError, Bind.bind, Except.bind, Nat.not_lt_of_ge slots, ite_false,
    Nat.not_lt_of_ge rows, order]
  rw [prefixStep]
  rcases failed with decoded | ⟨events, error, decoded, feed, rfl⟩
  · simp only [Nat.zero_add, ListFile.Multi.readFramesWith, decoded, Except.mapError, Bind.bind, Except.bind]
  · simp only [Nat.zero_add, ListFile.Multi.readFramesWith, decoded, feed, Except.mapError, Bind.bind,
      Except.bind, Function.comp_apply]

public theorem readGroup_frame_error {maxGroupSlots : Nat} {checked : Checked} {ordinal : Nat}
    {framed : ListFile.FramedGroup} {before after : List Page.Frame} {frame : Page.Frame}
    {remaining : Nat} {state : State} {cause : FrameError}
    (selected : checked.frameGroup ordinal = .ok framed)
    (slots : framed.chunk.metadata.numValues.toNat ≤ maxGroupSlots)
    (rows : framed.group.numRows.toNat ≤ checked.limits.page.maxRows)
    (order : framed.frames = before ++ frame :: after)
    (earlier : readFrames checked before 0 framed.chunk.metadata.numValues.toNat State.empty = .ok (remaining, state))
    (failed : readFrame checked remaining frame = .error cause ∨
      ∃ events error, readFrame checked remaining frame = .ok events ∧
        state.feed events = .error error ∧ cause = .data (.page error)) :
    readGroup maxGroupSlots checked ordinal = .error (.frame before.length frame.header.start cause) :=
  readGroupWith_frame_error (read := readFrame) (feedError := fun cause => .data (.page cause))
    selected slots rows order earlier failed

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Multi
