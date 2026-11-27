module

public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2

private theorem mapError_ok {α ε δ : Type} {input : Except ε α} {wrap : ε → δ} {out : α}
    (read : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases read
  rfl

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (read : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, read⟩

theorem planData_wire {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {page : DataPage}
    (planned : planData bound frame ordinal = .ok page) :
    page.frame = frame ∧ ∃ header, frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      page.params =
        ⟨⟨frame.value.compressedSize, frame.value.uncompressedSize⟩,
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.snappy.id,
          header.encoding, .v2 header.numNulls header.numRows header.repetitionBytes
            header.definitionBytes (some header.isCompressed)⟩ := by
  cases kind : frame.value.kind with
  | dataV2 header =>
    simp only [planData, kind] at planned
    split at planned
    · contradiction
    rename_i tag
    simp [FlatScan.int32PageParameters, kind, Pure.pure, Except.pure] at planned
    subst page
    exact ⟨rfl, header, rfl, not_not.mp tag, by simp⟩
  | dictionary _ | dataV1 _ | skipped _ => simp [planData, kind] at planned

theorem planData_badTag {bound : Bound} {frame : Page.Frame} {ordinal : Nat} {header : Page.DataV2}
    (kind : frame.value.kind = .dataV2 header) (wrong : header.encoding ≠ 0) :
    planData bound frame ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal frame (.encoding header.encoding))) := by
  simp [planData, kind, wrong]
  rfl

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) : GroupWire limits bound index checked := by
  have wire := Date.Leaf.Gzip.checkGroupFor_wire (plan := planData bound)
    (valid := fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page)
    (fun {frame ordinal page} planned => by
      have same := (planData_wire planned).1
      exact ⟨same, ordinal, by simpa only [same] using planned⟩) accepted
  refine ⟨wire, Nat.le_of_not_gt ?_⟩
  intro over
  simp only [checkGroup, Date.Leaf.Gzip.checkGroupFor, wire.selected, Except.mapError, Bind.bind,
    Except.bind, wire.codec, ne_self_iff_false, ite_false] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> contradiction

private theorem suffixWire_of_payload {frame : Page.Frame} {header : Page.DataV2} {stored plain : List UInt8}
    (exact : ScalarPage.ExactPayload (frame.value.compressedSize - header.definitionBytes)
      (frame.value.uncompressedSize - header.definitionBytes)
      (ScalarPage.v2Codec Payload.Codec.snappy.id (some header.isCompressed)) stored plain) :
    SuffixWire frame header stored plain := by
  obtain ⟨storedLength, plainLength, codec, selected, decode⟩ := exact
  refine ⟨storedLength, plainLength, ?_⟩
  cases flag : header.isCompressed with
  | false =>
    have same : Payload.Codec.uncompressed = codec := by
      apply Option.some.inj
      simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
    subst codec
    cases decode
    rfl
  | true =>
    have same : Payload.Codec.snappy = codec := by
      apply Option.some.inj
      simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
    subst codec
    exact decode

private theorem pageWire_exact {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {plannedAt : Nat} {slots : Slots}
    (planned : planData bound page.frame plannedAt = .ok page)
    (read : Date.Leaf.Gzip.PageWire limits source page slots) : PageWire limits source page slots := by
  obtain ⟨_, header, kind, tag, params⟩ := planData_wire planned
  obtain ⟨status, verified, scalar⟩ := read
  obtain ⟨slice, storedSize, storedBound, crc⟩ := Date.Leaf.Gzip.stored_exact verified
  obtain ⟨prepared, words, prep, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound scalar
  obtain ⟨layout, valid, body⟩ := ScalarPage.prepare_sound prep
  have expandedBound := Date.Leaf.Gzip.expanded_bound valid
  have counts := ScalarPage.decode_counts scalar
  simp only [params, ScalarPage.PreparedWire] at body
  simp only [params] at expandedBound counts
  obtain ⟨nulls, rows, repetition, defStored, defExpanded, defCap, definitions, suffix, length, split,
    levels, _, payload⟩ := body
  exact ⟨status, header, layout, definitions, suffix, prepared, words, kind, tag, verified, slice,
    storedSize, storedBound, expandedBound, by cases status <;> exact crc, rows, repetition, defStored, defExpanded, defCap,
    length, split, suffixWire_of_payload payload, valid, levels, plain, mask, ordered, counts.1, by omega⟩

theorem decodePage_wire {limits : Limits} {bound : Bound} {source : Bytes} {page : DataPage}
    {plannedAt readAt : Nat} {slots : Slots}
    (planned : planData bound page.frame plannedAt = .ok page)
    (read : decodePage limits source page readAt = .ok slots) : PageWire limits source page slots :=
  pageWire_exact planned (Date.Leaf.Gzip.decodePage_wire (mapError_ok read))

theorem decodePage_checksum_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {cause : Page.Checksum.Error}
    (failed : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .error cause) :
    decodePage limits source page ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal page.frame (.checksum cause))) := by
  rw [decodePage, Date.Leaf.Gzip.decodePage_checksum_error failed]
  rfl

theorem decodePage_scalar_error {limits : Limits} {source : Bytes} {page : DataPage}
    {ordinal : Nat} {status : Page.Checksum.Status} {cause : ScalarPage.Error}
    (admitted : Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status)
    (failed : ScalarPage.decode .int32 page.params limits.scalar
      (Page.Checksum.payloadBytes source page.frame) = .error cause) :
    decodePage limits source page ordinal =
      .error (.plain (Date.Leaf.Gzip.atFrame ordinal page.frame (.scalar cause))) := by
  simp [decodePage, Date.Leaf.Gzip.decodePage, admitted, failed, Except.mapError, Bind.bind, Except.bind]

private theorem paired_exact {limits : Limits} {bound : Bound} {data : List DataPage}
    {pages : List Slots}
    (paired : List.Forall₂ (Date.Leaf.Gzip.PageWire limits bound.snapshot.bytes) data pages)
    (planned : ∀ page ∈ data, ∃ ordinal, planData bound page.frame ordinal = .ok page) :
    List.Forall₂ (PageWire limits bound.snapshot.bytes) data pages ∧
      pages.map List.length = data.map (·.params.numValues) := by
  induction paired with
  | nil => exact ⟨.nil, rfl⟩
  | cons first _ ih =>
    obtain ⟨_, header⟩ := planned _ List.mem_cons_self
    have decoded := pageWire_exact header first
    obtain ⟨_, _, scalar⟩ := first
    obtain ⟨tail, count⟩ := ih (fun page member => planned page (List.mem_cons_of_mem _ member))
    exact ⟨.cons decoded tail, congrArg₂ List.cons (ScalarPage.decode_counts scalar).1 count⟩

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Snappy.V2.readGroup limits bound index = .ok slots) : SlotsWire limits bound index slots := by
  unfold Date.Leaf.Snappy.V2.readGroup at read
  obtain ⟨checked, planned, read⟩ := bind_ok read
  obtain ⟨pages, decoded, read⟩ := bind_ok read
  have zipped := (List.mapM_eq_ok_iff_forall₂.mp decoded).imp fun _ _ h =>
    Date.Leaf.Gzip.decodePage_wire (mapError_ok h)
  have paired : List.Forall₂ (Date.Leaf.Gzip.PageWire limits bound.snapshot.bytes) checked.data pages := by
    simpa using List.forall₂_map_left_iff.mpr zipped
  have wire := checkGroup_wire planned
  obtain ⟨original, count⟩ := paired_exact paired wire.1.data
  have same := (Except.ok.inj read).symm
  exact ⟨checked, pages, planned, wire, original, same, by
    rw [same, List.length_flatten, count, wire.1.rows]⟩

theorem readGroup_firstPageError {limits : Limits} {bound : Bound} {index ordinal : Nat}
    {checked : CheckedGroup} {page : DataPage} {before after : List (DataPage × Nat)}
    {prefixSlots : List Slots} {cause : GroupError}
    (admitted : checkGroup limits bound index = .ok checked)
    (split : checked.data.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodePage limits bound.snapshot.bytes item i) = .ok prefixSlots)
    (failed : decodePage limits bound.snapshot.bytes page ordinal = .error cause) :
    Date.Leaf.Snappy.V2.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Snappy.V2.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Snappy.V2
