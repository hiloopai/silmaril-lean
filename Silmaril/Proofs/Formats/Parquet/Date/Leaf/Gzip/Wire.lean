module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Gzip

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV1 header ∧ header.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
          header.encoding, .v1 header.definitionLevelEncoding header.repetitionLevelEncoding⟩ := by
  cases kind : frame.value.kind with
  | dataV1 header =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i tag
    simp [FlatScan.int32PageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, header, rfl, not_not.mp tag, by simp⟩
  | dictionary _ | dataV2 _ | skipped _ => simp [planData, kind] at planned

private theorem pages_plan {ε : Type} {plan : Page.Frame → Nat → Except ε DataPage}
    {valid : DataPage → Prop} {frames : List Page.Frame} {data : List DataPage}
    (keeps : ∀ {frame ordinal page}, plan frame ordinal = .ok page → page.frame = frame ∧ valid page)
    (planned : frames.zipIdx.mapM (fun (frame, ordinal) => plan frame ordinal) = .ok data) :
    data.map (·.frame) = frames ∧ ∀ page ∈ data, valid page := by
  have indexed := (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun _ _ h => keeps h
  have paired : List.Forall₂ (fun frame page => page.frame = frame ∧ valid page) frames data := by
    rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff]
    exact indexed
  clear planned indexed
  induction paired with
  | nil => simp
  | cons head _ ih =>
    refine ⟨by simp [head.1, ih.1], ?_⟩
    intro page member
    rcases List.mem_cons.mp member with rfl | later
    · exact head.2
    · exact ih.2 page later

theorem checkGroupWith_wire {ε : Type} {wrap : GroupError → ε}
    {plan : Page.Frame → Nat → Except ε DataPage} {valid : DataPage → Prop}
    {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (keeps : ∀ {frame ordinal page}, plan frame ordinal = .ok page → page.frame = frame ∧ valid page)
    (accepted : checkGroupWith wrap plan limits bound index = .ok checked) :
    GroupWire limits bound index checked valid := by
  unfold checkGroupWith at accepted
  obtain ⟨chunk, selected, accepted⟩ := bind_ok accepted
  simp only at accepted
  split at accepted
  · contradiction
  rename_i codec
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted
  · contradiction
  rename_i stored
  obtain ⟨frames, framed, accepted⟩ := bind_ok accepted
  split at accepted
  · contradiction
  rename_i expanded
  have original := mapError_ok framed
  cases frames with
  | nil => contradiction
  | cons first rest =>
    dsimp only at accepted
    split at accepted
    · contradiction
    rename_i dataOffset
    obtain ⟨data, planned, accepted⟩ := bind_ok accepted
    split at accepted
    · contradiction
    rename_i count
    cases Except.ok.inj accepted
    obtain ⟨order, headers⟩ := pages_plan (plan := plan) keeps planned
    have head := congrArg List.head? order
    rw [List.head?_map] at head
    have offset := congrArg (Option.map (fun frame : Page.Frame => (frame.header.start : Int))) head
    refine ⟨mapError_ok selected, not_not.mp codec, Nat.le_of_not_gt stored, ?_, ?_, ?_, ?_,
      headers, not_not.mp count⟩
    · simpa [CheckedGroup.frames, order] using Nat.le_of_not_gt expanded
    · simpa [CheckedGroup.frames, order] using original
    · simpa [CheckedGroup.frames, order] using (Page.readChunk_chain original).2.2
    · simpa [Option.map_map, Function.comp_def, ← not_not.mp dataOffset] using offset

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked := by
  apply checkGroupWith_wire _ accepted
  intro frame ordinal page read
  have decoded := mapError_ok read
  have same := (planData_wire decoded).1
  exact ⟨same, by simpa only [same] using decoded⟩

theorem decodePage_wire {limits : Limits} {source : Bytes} {page : DataPage} {ordinal : Nat}
    {slots : Slots} (read : decodePage limits source page ordinal = .ok slots) :
    PageWire limits source page slots := by
  unfold decodePage at read
  obtain ⟨status, verified, decoded⟩ := bind_ok read
  exact ⟨status, mapError_ok verified, mapError_ok decoded⟩

theorem stored_exact {cap : Nat} {source : Bytes} {frame : Page.Frame} {status : Page.Checksum.Status}
    (verified : Page.Checksum.verify cap source frame = .ok status) :
    let stored := Page.Checksum.payloadBytes source frame
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc := by
  cases status with
  | absent =>
    obtain ⟨withinCap, extent, absent⟩ := Page.Checksum.verify_absent_iff.mp verified
    obtain ⟨slice, size⟩ := Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ withinCap, absent⟩
  | valid crc =>
    obtain ⟨withinCap, extent, header, computed⟩ := Page.Checksum.verify_valid_iff.mp verified
    obtain ⟨slice, size⟩ := Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ withinCap, header, computed⟩

theorem expanded_bound {params : ScalarPage.Parameters} {limits : ScalarPage.Limits}
    {source : Bytes} {layout : FlatPage.Layout}
    (valid : ScalarPage.validate params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  unfold ScalarPage.validate ScalarPage.validateFor at valid
  dsimp only at valid
  split_ifs at valid with tag extent compressed expanded
  exact Nat.le_of_not_gt expanded

theorem pageWire_exact {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {slots : Slots} (planned : planData bound page.frame = .ok page)
    (read : PageWire limits source page slots) :
    let stored := Page.Checksum.payloadBytes source page.frame
    ∃ (status : Page.Checksum.Status), ∃ layout expanded prepared words,
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
      (match status with
       | .absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      Compression.Gzip.decoder stored.toList = some (expanded, []) ∧
      expanded.length = page.frame.value.uncompressedSize ∧ expanded.length ≤ limits.scalar.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params limits.scalar layout stored prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧ slots.length = page.params.numValues := by
  obtain ⟨_, header, _, _, params⟩ := planData_wire planned
  obtain ⟨status, verified, decoded⟩ := read
  obtain ⟨slice, storedSize, storedCap, crc⟩ := stored_exact verified
  obtain ⟨prepared, words, prep, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, valid, layoutWire⟩ := ScalarPage.prepare_sound prep
  have version : page.params.version = .v1 header.definitionLevelEncoding header.repetitionLevelEncoding := by
    rw [params]
  obtain ⟨_, expanded, _, _, exactPayload, _, _⟩ := ScalarPage.prepared_v1_slices version prep
  obtain ⟨_, size, codec, codecId, expansion⟩ := exactPayload
  rw [params] at codecId
  change some Payload.Codec.gzip = some codec at codecId
  cases Option.some.inj codecId
  have gzip : Compression.Gzip.decoder (Page.Checksum.payloadBytes source page.frame).toList =
      some (expanded, []) := by
    cases expansion with
    | gzip decoded => exact decoded
  refine ⟨status, layout, expanded, prepared, words, slice, storedSize, storedCap, by cases status <;> exact crc,
    gzip, ?_, size.trans_le (expanded_bound valid), layoutWire, plain, mask, ordered,
    (ScalarPage.decode_counts decoded).1⟩
  simpa [params] using size

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Gzip.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Gzip.readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have zipped := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ h => decodePage_wire h
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages := by
    simpa using List.forall₂_map_left_iff.mpr zipped
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded zipped
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons first _ tail =>
      obtain ⟨_, _, scalar⟩ := first
      exact congrArg₂ List.cons (ScalarPage.decode_counts scalar).1 tail
  have wire := checkGroup_wire planned
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes page ordinal = .error cause) :
    Date.Leaf.Gzip.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Gzip.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip
