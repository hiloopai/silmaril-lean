module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Defs
public import Silmaril.Formats.Compression.Checksum.CRC32Spec
import all Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.V2

open Silmaril.Formats Parquet
open Silmaril.Formats.Parquet.Date.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Date.Leaf.Gzip (CheckedGroup DataPage GroupWire PageWire)
open Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2

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
          ⟨0, if bound.field.layout == .required then 0 else 1⟩, header.numValues, Payload.Codec.gzip.id,
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

theorem checkGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {checked : CheckedGroup}
    (accepted : checkGroup limits bound index = .ok checked) :
    GroupWire limits bound index checked (fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page) := by
  apply Date.Leaf.Gzip.checkGroupWith_wire (plan := planData bound) _ accepted
  intro frame ordinal page planned
  have same := (planData_wire planned).1
  exact ⟨same, ordinal, by simpa only [same] using planned⟩

theorem decodePage_wire {limits : Limits} {source : Bytes} {page : DataPage} {ordinal : Nat}
    {slots : Slots} (read : decodePage limits source page ordinal = .ok slots) :
    PageWire limits source page slots :=
  Date.Leaf.Gzip.decodePage_wire (mapError_ok read)

theorem pageWire_exact {limits : Limits} {bound : Bound} {source : Bytes}
    {page : DataPage} {ordinal : Nat} {slots : Slots}
    (planned : planData bound page.frame ordinal = .ok page) (read : PageWire limits source page slots) :
    let stored := Page.Checksum.payloadBytes source page.frame
    ∃ (status : Page.Checksum.Status), ∃ header layout definitions encoded,
      ∃ (prepared : ScalarPage.Prepared), ∃ words,
      page.frame.value.kind = .dataV2 header ∧ header.encoding = 0 ∧
      source.slice? page.frame.payload.start (some page.frame.payload.stop) = some stored ∧
      stored.length = page.frame.value.compressedSize ∧ stored.length ≤ limits.scalar.compressedBytes ∧
      page.frame.value.uncompressedSize ≤ limits.scalar.uncompressedBytes ∧
      (match status with
       | .absent => page.frame.value.crc = none
       | .valid crc => page.frame.value.crc = some crc ∧ Compression.crc32Spec stored.toList = crc) ∧
      header.repetitionBytes = 0 ∧ definitions.length = header.definitionBytes ∧
      stored.toList = definitions.toList ++ encoded ∧
      encoded.length = page.frame.value.compressedSize - header.definitionBytes ∧
      prepared.scalars.length = page.frame.value.uncompressedSize - header.definitionBytes ∧
      (if header.isCompressed then Compression.Gzip.decoder encoded = some (prepared.scalars.toList, [])
        else encoded = prepared.scalars.toList) ∧
      FlatPage.readMask layout header.numValues limits.scalar.levels definitions = .ok prepared.mask ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words ∧
      slots.length = header.numValues ∧ header.numRows = header.numValues ∧
      (slots.filterMap id).length + header.numNulls = header.numValues := by
  obtain ⟨_, header, kind, tag, params⟩ := planData_wire planned
  obtain ⟨status, crcCheck, decoded⟩ := read
  obtain ⟨slice, storedSize, storedCap, crc⟩ := Date.Leaf.Gzip.stored_exact crcCheck
  obtain ⟨prepared, words, prep, plain, mask, ordered, _, _⟩ := ScalarPage.decode_sound decoded
  obtain ⟨layout, valid, body⟩ := ScalarPage.prepare_sound prep
  have sizes := Date.Leaf.Gzip.expanded_bound valid
  have counts := ScalarPage.decode_counts decoded
  simp only [params, ScalarPage.PreparedWire] at body
  simp only [params] at counts sizes
  obtain ⟨nulls, rows, repetition, _, _, _, definitions, encoded, length, split, levels, _, payload⟩ := body
  obtain ⟨encodedSize, expandedSize, codec, selected, expansion⟩ := payload
  have suffix : if header.isCompressed then
        Compression.Gzip.decoder encoded = some (prepared.scalars.toList, [])
      else encoded = prepared.scalars.toList := by
    cases flag : header.isCompressed with
    | false =>
      have codecIs : Payload.Codec.uncompressed = codec := by
        apply Option.some.inj
        simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
      subst codec
      cases expansion
      simp
    | true =>
      have codecIs : Payload.Codec.gzip = codec := by
        apply Option.some.inj
        simpa [ScalarPage.v2Codec, flag, Payload.Codec.ofId_id] using selected
      subst codec
      cases expansion with
      | gzip complete => simpa using complete
  refine ⟨status, header, layout, definitions, encoded, prepared, words, kind, tag,
    slice, storedSize, storedCap, sizes, by cases status <;> exact crc,
    repetition, length, split, encodedSize, by simpa using expandedSize,
    suffix, levels, plain, mask, ordered, counts.1, rows, ?_⟩
  have present := counts.2
  omega

theorem readGroup_wire {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Date.Leaf.Gzip.V2.readGroup limits bound index = .ok slots) :
    ∃ checked pages, checkGroup limits bound index = .ok checked ∧
      GroupWire limits bound index checked (fun page => ∃ ordinal, planData bound page.frame ordinal = .ok page) ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes) checked.data pages ∧
      slots = pages.flatten ∧ slots.length = checked.selection.group.numRows.toNat := by
  unfold Date.Leaf.Gzip.V2.readGroup at read
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
    Date.Leaf.Gzip.V2.readGroup limits bound index = .error cause := by
  simp [Date.Leaf.Gzip.V2.readGroup, admitted, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Gzip.V2
