module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip.Defs
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Fallback.Gzip
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

theorem planData_wire {bound : Bound} {frame : Page.Frame} {page : DataPage}
    (planned : planData bound frame = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV1 header ∧
      (header.encoding = 8 ∨ header.encoding = 0) ∧
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
    exact ⟨rfl, header, rfl, by tauto, by simp⟩
  | dictionary _ | dataV2 _ | skipped _ => simp [planData, kind] at planned

theorem planPages_wire {bound : Bound} {frames : List Page.Frame} {pages : List DataPage}
    (planned : planPages bound frames = .ok pages) :
    pages.map (·.frame) = frames ∧ (∀ page ∈ pages, planData bound page.frame = .ok page) ∧
      Date.Leaf.Fallback.Ordered pages :=
  Date.Leaf.Fallback.planPagesWith_wire (fun planned => (planData_wire planned).1) planned

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (readEntries limits)
      (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data :=
  Date.Leaf.Dictionary.Snappy.checkGroupWithCodec_wire planPages_wire accepted

theorem transition_totals {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    ∃ references plain, checked.data = references ++ plain ∧ references ≠ [] ∧ plain ≠ [] ∧
      (∀ page ∈ references, page.params.encoding = 8) ∧
      (∀ page ∈ plain, page.params.encoding = 0) ∧
      (references.map (·.params.numValues)).sum + (plain.map (·.params.numValues)).sum =
        checked.selection.group.numRows.toNat ∧
      checked.dictionary.value.uncompressedSize +
        ((references.map (·.frame.value.uncompressedSize)).sum +
          (plain.map (·.frame.value.uncompressedSize)).sum) ≤ limits.maxExpandedChunkBytes := by
  obtain ⟨wire, references, plain, order, first, second, refs, raw⟩ := checkGroup_wire accepted
  exact ⟨references, plain, order, first, second, refs, raw,
    by simpa [order, List.sum_append] using wire.rows,
    by simpa [Date.Leaf.Dictionary.Snappy.CheckedGroup.frames, order, List.sum_append, List.map_map,
      Function.comp_def] using wire.expandedCap⟩

private theorem storedMember {source : Bytes} {frame : Page.Frame} {storedCap expandedCap : Nat}
    {status : Page.Checksum.Status} {expanded : List UInt8}
    (verified : Page.Checksum.verify storedCap source frame = .ok status)
    (decoded : Payload.Decodes frame.value.uncompressedSize .gzip
      (Page.Checksum.payloadBytes source frame).toList expanded)
    (size : expanded.length = frame.value.uncompressedSize) (cap : expanded.length ≤ expandedCap) :
    StoredMember source frame storedCap expandedCap expanded := by
  obtain ⟨slice, storedSize, storedBound, crc⟩ := Date.Leaf.Gzip.stored_exact verified
  refine ⟨?_, slice, storedSize, storedSize ▸ storedBound, ?_, size, cap⟩
  · cases status with
    | absent => exact .inl crc
    | valid word => exact .inr ⟨word, crc⟩
  · cases decoded with
    | gzip decoded => exact decoded

theorem readEntries_wire {limits : Limits} {source : Bytes} {frame : Page.Frame}
    {entries : List Int32} (read : readEntries limits source frame = .ok entries) :
    let bounds := Date.Leaf.Dictionary.Snappy.dictionaryBounds limits.toDictionaryLimits frame
    ∃ header expanded, frame.value.kind = .dictionary header ∧ header.encoding = 0 ∧
      header.numValues ≤ limits.maxEntries ∧
      StoredMember source frame bounds.compressedLimit bounds.outputLimit expanded ∧
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
    obtain ⟨_, verified, read⟩ := bind_ok read
    obtain ⟨expanded, decoded, read⟩ := bind_ok read
    obtain ⟨codec, id, expansion, _, _, size, cap⟩ := Payload.decode_sound (mapError_ok decoded)
    change some Payload.Codec.gzip = some codec at id
    cases Option.some.inj id
    have words := mapError_ok read
    obtain ⟨_, _, _, rows, _, rfl⟩ := Plain.decodeFixedWidth_ok_iff.mp
      (by simpa only [Plain.decodeInt32] using words)
    exact ⟨header, expanded, rfl, not_not.mp encoding, Nat.le_of_not_gt count,
      storedMember (mapError_ok verified) expansion size cap, words, by simpa using rows⟩

private theorem expanded_bound {encoding : Int} {params : ScalarPage.Parameters}
    {limits : ScalarPage.Limits} {source : Bytes} {layout : FlatPage.Layout}
    (valid : ScalarPage.validateFor encoding params limits source = .ok layout) :
    params.sizes.uncompressed ≤ limits.uncompressedBytes := by
  unfold ScalarPage.validateFor at valid
  dsimp only at valid
  split_ifs at valid with tag extent compressed expanded
  exact Nat.le_of_not_gt expanded

private theorem dataMember {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {status : Page.Checksum.Status} {prepared : ScalarPage.Prepared} {encoding : Int}
    (planned : planData bound page.frame = .ok page)
    (verified : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status)
    (prep : ScalarPage.prepareFor encoding page.params limits.scalar
      (Page.Checksum.payloadBytes source page.frame) = .ok prepared) :
    ∃ expanded layout sections,
      StoredMember source page.frame limits.scalar.compressedBytes limits.scalar.uncompressedBytes expanded ∧
      FlatPage.split layout limits.scalar.levels.bytes (.v1 (Bytes.ofList expanded)) = .ok sections ∧
      FlatPage.readMask layout page.params.numValues limits.scalar.levels sections.definitions =
        .ok prepared.mask ∧
      prepared.scalars = sections.scalars := by
  obtain ⟨_, header, _, _, params⟩ := planData_wire planned
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepareFor_sound prep
  have version : page.params.version = .v1 header.definitionLevelEncoding header.repetitionLevelEncoding := by
    rw [params]
  unfold ScalarPage.PreparedWire at wire
  rw [version] at wire
  obtain ⟨_, _, expanded, sections, exactBody, split, mask, scalars⟩ := wire
  obtain ⟨_, size, codec, id, expansion⟩ := exactBody
  rw [params] at id
  change some Payload.Codec.gzip = some codec at id
  cases Option.some.inj id
  exact ⟨expanded, layout, sections, storedMember verified (by simpa [params] using expansion)
    (by simpa [params] using size) (size.trans_le (expanded_bound valid)), split, mask, scalars⟩

theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {entries : Array Int32}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame = .ok page)
    (decoded : decodePage limits source entries page ordinal = .ok slots) :
    PageWire limits source entries page slots := by
  unfold decodePage decodePageWith at decoded
  obtain ⟨status, verified, decoded⟩ := bind_ok decoded
  have crc := Date.Leaf.Dictionary.Snappy.verifyData_wire (mapError_ok verified)
  by_cases plain : page.params.encoding = 0
  · simp only [plain, ite_true] at decoded
    have read := mapError_ok decoded
    obtain ⟨prepared, words, prep, signed, mask, order, _, _⟩ := ScalarPage.decode_sound read
    obtain ⟨expanded, layout, sections, member, split, levels, scalars⟩ :=
      dataMember planned crc (show ScalarPage.prepareFor 0 .. = _ from prep)
    exact ⟨(ScalarPage.decode_counts read).1, expanded, layout, sections, prepared, member, split,
      levels, scalars, mask, .inr ⟨plain, order ▸ signed⟩⟩
  · simp only [plain, ite_false] at decoded
    have read := mapError_ok decoded
    obtain ⟨_, _, _, tag, params⟩ := planData_wire planned
    have references : page.params.encoding = 8 := by
      rw [params] at plain ⊢
      exact tag.resolve_right plain
    obtain ⟨_, prepared, indices, prep, runs, mask, ordered⟩ := DictionaryIndex.decode_ok_iff.mp read
    obtain ⟨_, width, bytes, octets, maxWidth, _, _, wire⟩ := DictionaryIndex.readIndices_ok_iff.mp runs
    obtain ⟨expanded, layout, sections, member, split, levels, scalars⟩ := dataMember planned crc prep
    exact ⟨(DictionaryIndex.decode_counts read).1, expanded, layout, sections, prepared, member, split,
      levels, scalars, mask, .inl ⟨references, width, bytes, indices, octets, maxWidth, wire, ordered⟩⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Fallback.Gzip.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      Date.Leaf.Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip (readEntries limits)
        (fun page => planData bound page.frame = .ok page) ∧ Date.Leaf.Fallback.Ordered checked.data ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Fallback.Gzip.readGroup readGroupWith at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  obtain ⟨wire, phases⟩ := checkGroup_wire planned
  have zipped := List.mapM_eq_ok_iff_forall₂.mp decoded
  have paired : List.Forall₂ (PageWire limits bound.snapshot.bytes checked.entries.toArray) checked.data pages := by
    have raw : List.Forall₂
        (fun page out => ∃ ordinal, decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal =
          .ok out) checked.data pages := by
      rw [← List.zipIdx_map_fst 1 checked.data, List.forall₂_map_left_iff]
      exact zipped.imp fun item _ read => ⟨item.2, read⟩
    have admitted := wire.data
    clear wire phases zipped decoded planned read
    generalize checked.data = data at admitted raw ⊢
    induction raw with
    | nil => exact .nil
    | cons head _ ih =>
      obtain ⟨_, decoded⟩ := head
      exact .cons (decodePage_wire (admitted _ (List.mem_cons_self ..)) decoded)
        (ih fun page member => admitted page (List.mem_cons_of_mem _ member))
  have count : pages.map List.length = checked.data.map (·.params.numValues) := by
    clear read decoded wire phases zipped
    generalize checked.data = data at paired ⊢
    induction paired with
    | nil => rfl
    | cons head _ tail => exact congrArg₂ List.cons head.count tail
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, phases, paired, same, by
    rw [same, List.length_flatten, count, wire.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes checked.entries.toArray item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes checked.entries.toArray page ordinal = .error cause) :
    Date.Leaf.Fallback.Gzip.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Fallback.Gzip.readGroup, readGroupWith, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Fallback.Gzip
