module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots selectChunk)
open Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy
open Silmaril.Formats.Parquet.DictionaryChunk (DataPage)

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem stored_verified {cap : Nat} {source : Bytes} {frame : Page.Frame}
    {status : Page.Checksum.Status} (verified : Page.Checksum.verify cap source frame = .ok status) :
    let stored := Page.Checksum.payloadBytes source frame
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
      stored.length = frame.value.compressedSize ∧ stored.length ≤ cap ∧
      match status with
      | .absent => frame.value.crc = none
      | .valid crc => frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc := by
  cases status with
  | absent =>
    obtain ⟨cap, extent, absent⟩ := Page.Checksum.verify_absent_iff.mp verified
    obtain ⟨slice, size⟩ := Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ cap, absent⟩
  | valid crc =>
    obtain ⟨cap, extent, header, computed⟩ := Page.Checksum.verify_valid_iff.mp verified
    obtain ⟨slice, size⟩ := Page.Checksum.payload_exact extent
    exact ⟨slice, size, size ▸ cap, header, computed⟩

theorem readEntries_wire {limits : Limits} {source : Bytes} {frame : Page.Frame}
    {entries : List Int32} (read : readEntries limits source frame = .ok entries) :
    ∃ header status expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      Page.Checksum.verify (dictionaryBounds limits frame).compressedLimit source frame = .ok status ∧
      Payload.Decodes frame.value.uncompressedSize .snappy (Page.Checksum.payloadBytes source frame).toList
        expanded ∧
      expanded.length = frame.value.uncompressedSize ∧ expanded.length ≤ (dictionaryBounds limits frame).outputLimit ∧
      Plain.decodeInt32 header.numValues (Bytes.ofList expanded) = .ok entries ∧
      entries.length = header.numValues := by
  cases kind : frame.value.kind with
  | dataV1 _ | dataV2 _ | skipped _ => simp [readEntries, kind] at read
  | dictionary header =>
    simp only [readEntries, kind] at read
    split at read
    · contradiction
    rename_i encoding
    split at read
    · contradiction
    rename_i count
    split at read
    · contradiction
    obtain ⟨status, verified, read⟩ := bind_ok read
    obtain ⟨expanded, decoded, read⟩ := bind_ok read
    obtain ⟨codec, id, expansion, _, _, size, cap⟩ := Payload.decode_sound (mapError_ok decoded)
    change some Payload.Codec.snappy = some codec at id
    cases Option.some.inj id
    have words := mapError_ok read
    obtain ⟨_, raw, _, rows, _, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp
      (by simpa only [Plain.decodeInt32] using words)
    exact ⟨header, status, expanded, rfl, not_not.mp encoding, Nat.le_of_not_gt count,
      mapError_ok verified, expansion, size, cap, words, by simpa using rows⟩

theorem planDataWith_wire {admits : Int → Bool} {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planDataWith admits bound frame = .ok page) :
    page.frame = frame ∧ admits page.params.encoding = true ∧
      ∃ base, FlatScan.int32PageParameters bound.field frame.value = some base ∧
        page.params = { base with codec := Payload.Codec.snappy.id } := by
  cases parameters : FlatScan.int32PageParameters bound.field frame.value with
  | none => simp [planDataWith, parameters] at planned
  | some base =>
    simp only [planDataWith, parameters] at planned
    split at planned
    · contradiction
    rename_i encoding
    cases Except.ok.inj planned
    exact ⟨rfl, by simpa using encoding, base, rfl, rfl⟩

theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ page.params.encoding = 8 ∧
      ∃ base, FlatScan.int32PageParameters bound.field frame.value = some base ∧
        page.params = { base with codec := Payload.Codec.snappy.id } := by
  obtain ⟨same, admitted, params⟩ := planDataWith_wire planned
  exact ⟨same, by simpa using admitted, params⟩

private theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {data : List DataPage}
    (planned : planPages (planData bound) frames = .ok data) :
    data.map (·.frame) = frames ∧ ∀ page ∈ data, planData bound page.frame = .ok page := by
  unfold planPages at planned
  have zipped := (List.mapM_eq_ok_iff_forall₂.mp planned).imp fun _ _ h => mapError_ok h
  have paired : List.Forall₂ (fun frame page => planData bound frame = .ok page) frames data := by
    rw [← List.zipIdx_map_fst 1 frames, List.forall₂_map_left_iff]
    exact zipped
  clear planned zipped
  induction paired with
  | nil => simp
  | cons head _ ih =>
    have same := (planData_wire head).1
    refine ⟨by simp [same, ih.1], ?_⟩
    intro page member
    rcases List.mem_cons.mp member with rfl | rest
    · rwa [same]
    · exact ih.2 page rest

theorem checkGroupWithCodec_wire {ε : Type} {codec : Payload.Codec} {wrap : GroupError → ε}
    {readDictionary : Bytes → Page.Frame → Except PageError (List Int32)}
    {plan : List Page.Frame → Except ε (List DataPage)} {admitted : DataPage → Prop}
    {valid : List DataPage → Prop} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup}
    (keeps : ∀ {frames data}, plan frames = .ok data →
      data.map (·.frame) = frames ∧ (∀ page ∈ data, admitted page) ∧ valid data)
    (accepted : checkGroupWithCodec codec wrap readDictionary plan limits bound index = .ok checked) :
    GroupWireWith limits bound index checked codec readDictionary admitted ∧ valid checked.data := by
  unfold checkGroupWithCodec at accepted
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
  have originalFrames := mapError_ok framed
  cases frames with
  | nil => contradiction
  | cons dictionary rest =>
    dsimp only at accepted
    split at accepted
    · contradiction
    rename_i dictionaryOffset
    cases rest with
    | nil => contradiction
    | cons first following =>
      dsimp only at accepted
      split at accepted
      · contradiction
      rename_i dataOffset
      obtain ⟨data, planned, accepted⟩ := bind_ok accepted
      split at accepted
      · contradiction
      rename_i count
      obtain ⟨entries, decoded, accepted⟩ := bind_ok accepted
      cases Except.ok.inj accepted
      obtain ⟨order, dataReads, validData⟩ := keeps planned
      have head := congrArg List.head? order
      rw [List.head?_map] at head
      have offset := congrArg (Option.map (fun frame : Page.Frame => (frame.header.start : Int))) head
      refine ⟨⟨mapError_ok selected, not_not.mp codec, Nat.le_of_not_gt stored, ?_, ?_, ?_,
        not_not.mp dictionaryOffset, ?_, mapError_ok decoded, dataReads, not_not.mp count⟩, validData⟩
      · simpa [CheckedGroup.frames, order] using Nat.le_of_not_gt expanded
      · simpa [CheckedGroup.frames, order] using originalFrames
      · simpa [CheckedGroup.frames, order] using (Page.readChunk_chain originalFrames).2.2
      · simpa [Option.map_map, Function.comp_def, ← not_not.mp dataOffset] using offset

theorem checkGroupWith_wire {ε : Type} {wrap : GroupError → ε}
    {plan : List Page.Frame → Except ε (List DataPage)} {admits : Int → Bool}
    {valid : List DataPage → Prop} {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup}
    (keeps : ∀ {frames data}, plan frames = .ok data →
      data.map (·.frame) = frames ∧ (∀ page ∈ data, planDataWith admits bound page.frame = .ok page) ∧ valid data)
    (accepted : checkGroupWith wrap plan limits bound index = .ok checked) :
    GroupWire limits bound index checked admits ∧ valid checked.data := by
  obtain ⟨wire, validData⟩ := checkGroupWithCodec_wire keeps accepted
  exact ⟨⟨wire.selected, wire.codec, wire.storedCap, wire.expandedCap, wire.frames, wire.chain,
    wire.dictionaryOffset, wire.dataOffset, wire.dictionary, wire.data, wire.rows⟩, validData⟩

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat}
    {checked : CheckedGroup} (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked :=
  (checkGroupWith_wire (valid := fun _ => True) (admits := (· == 8))
    (fun planned => let ⟨order, data⟩ := planPages_wire planned; ⟨order, data, trivial⟩) accepted).1

theorem verifyData_wire {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {status : Page.Checksum.Status}
    (verified : verifyData limits source page ordinal = .ok status) :
    Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status :=
  mapError_ok verified

theorem decodePage_wire {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (read : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  unfold decodePage at read
  obtain ⟨status, verified, decoded⟩ := bind_ok read
  exact ⟨status, verifyData_wire verified, mapError_ok decoded⟩

private theorem expanded_bound {encoding : Int} {params : ScalarPage.Parameters}
    {limits : ScalarPage.Limits} {source : Bytes} {layout : FlatPage.Layout}
    (checked : ScalarPage.validateFor encoding params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  unfold ScalarPage.validateFor at checked
  dsimp only at checked
  split_ifs at checked with tag extent compressed expanded
  exact Nat.le_of_not_gt expanded

theorem pageWire_exact {limits : Limits} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {slots : Slots} (read : PageWire limits source entries page slots) :
    let body := Page.Checksum.payloadBytes source page.frame
    ∃ status layout prepared width runs indices,
      Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
      page.params.sizes.uncompressed ≤ limits.scalar.uncompressedBytes ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
      slots.length = page.params.numValues := by
  obtain ⟨status, crc, decoded⟩ := read
  obtain ⟨_, prepared, refs, prep, indices, mask, ordered⟩ := DictionaryIndex.decode_ok_iff.mp decoded
  obtain ⟨layout, valid, exactBody⟩ := ScalarPage.prepareFor_sound prep
  obtain ⟨_, width, runs, octets, maxWidth, _, _, wire⟩ := DictionaryIndex.readIndices_ok_iff.mp indices
  exact ⟨status, layout, prepared, width, runs, refs, crc, expanded_bound valid, exactBody,
    octets, maxWidth, wire, mask, ordered, (DictionaryIndex.decode_counts decoded).1⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Dictionary.Snappy.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧ GroupWire limits bound index checked ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Dictionary.Snappy.readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have zipped := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp (fun _ _ h => decodePage_wire h)
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray)
      checked.data pages := by
    simpa using List.forall₂_map_left_iff.mpr zipped
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded zipped
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail =>
      obtain ⟨_, _, decoded⟩ := head
      exact congrArg₂ List.cons (DictionaryIndex.decode_counts decoded).1 tail
  have wire := checkGroup_wire planned
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    Date.Leaf.Dictionary.Snappy.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Dictionary.Snappy.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary.Snappy
