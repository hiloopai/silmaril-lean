module

public import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi.Defs
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Multi.Thms
import Silmaril.Formats.Parquet.ListFile.RequiredContainer.V2.Thms
import Silmaril.Formats.Parquet.ListFile.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open ListFile.RequiredContainer (Checked)
open ListFile.RequiredContainer.V2 (event_counts sections_physical)
open ListFile.RequiredContainer.V2.Snappy (readEvents readEvents_wire StoredWire)
open ListFile.RequiredContainer.V2.Snappy.Multi
open ListPage (Event Row)

public theorem readFrame_wire {limits : Limits} {checked : Checked} {remaining : Nat} {frame : Page.Frame}
    {events : List Event} (h : readFrame limits checked remaining frame = .ok events) :
    FrameWire limits checked frame events ∧ events.length ≤ remaining := by
  unfold readFrame at h
  split at h
  · rename_i info kind
    split at h
    · contradiction
    rename_i encoding
    split at h
    · contradiction
    rename_i slotCap
    split at h
    · contradiction
    rename_i rowCap
    have wire := readEvents_wire kind h
    obtain ⟨_, _, sections, _, _, _⟩ := wire.data
    exact ⟨⟨info, kind, not_not.mp encoding, Nat.le_of_not_gt rowCap, wire⟩,
      sections.count ▸ Nat.le_of_not_gt slotCap⟩
  · contradiction

public theorem frame_levels {limits : Limits} {checked : Checked} {frame : Page.Frame} {events : List Event}
    (h : FrameWire limits checked frame events) :
    ∃ info sections reps defs,
      frame.value.kind = .dataV2 info ∧ StoredWire limits.toSnappyLimits checked frame info sections ∧
      Hybrid.Wire 1 info.numValues sections.repetition.toList reps ∧
      Hybrid.Wire 2 info.numValues sections.definition.toList defs ∧
      reps.length = info.numValues ∧ defs.length = info.numValues ∧
      (reps = [] ∨ reps.head? = some 0) ∧ reps.count 0 = info.numRows ∧
      defs.countP (· != 2) = info.numNulls ∧ sections.scalars.length = 4 * (info.numValues - info.numNulls) ∧
      Plain.decodeInt32 (info.numValues - info.numNulls) sections.scalars =
        .ok (events.filterMap (fun event => event.wire.2.2)) := by
  obtain ⟨info, kind, _, _, wire⟩ := h.data
  obtain ⟨sections, stored, physical, boundary, rows, nulls⟩ := wire.data
  obtain ⟨reps, defs, repWire, defWire, repLength, defLength, rowTotal, nullTotal, ordered⟩ :=
    event_counts physical rows nulls
  obtain ⟨read, extent⟩ := sections_physical physical
  change ListFile.RequiredContainer.V2.missingSlots events = info.numNulls at nulls
  rw [nulls] at read extent
  refine ⟨info, sections, reps, defs, kind, stored, repWire, defWire, repLength, defLength, ?_, rowTotal,
    nullTotal, extent, read⟩
  rw [← ordered]
  cases events with
  | nil => exact Or.inl rfl
  | cons event tail =>
    cases event with
    | nullList => exact Or.inr rfl
    | emptyList => exact Or.inr rfl
    | first item => exact Or.inr rfl
    | next item => contradiction

public theorem readGroup_wire {limits : Limits} {checked : Checked} {ordinal : Nat} {rows : List Row}
    (h : readGroup limits checked ordinal = .ok rows) : GroupWire limits checked ordinal rows := by
  apply ListFile.RequiredContainer.V2.Multi.readGroupWith_wire (read := readFrame limits)
    (feedError := ListFile.Multi.Snappy.FrameError.page) ListFile.frameGroupFor_wire ?_ h
  intro remaining frame events decoded
  obtain ⟨wire, bound⟩ := readFrame_wire decoded
  obtain ⟨info, kind, _, _, frameWire⟩ := wire.data
  obtain ⟨sections, _, physical, _, rows, absent⟩ := frameWire.data
  exact ⟨wire, ⟨info, sections.repetition, sections.definition, sections.scalars, kind, physical, rows, absent⟩, bound⟩

end Silmaril.Proofs.Formats.Parquet.ListFile.RequiredContainer.V2.Snappy.Multi
