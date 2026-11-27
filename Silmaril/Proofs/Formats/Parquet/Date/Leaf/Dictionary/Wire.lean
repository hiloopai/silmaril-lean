module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs
import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.DictionaryChunk.Thms
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary

open Silmaril.Formats Parquet Date.Leaf Date.Leaf.Dictionary

private theorem forAllMapM {ε α β : Type} (decode : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM decode = .ok ys →
      List.Forall₂ (fun x y => decode x = .ok y) xs ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases h; exact .nil
  | cons x xs ih =>
    intro ys h
    cases head : decode x with
    | error cause => simp [List.mapM_cons, head, Bind.bind, Except.bind] at h
    | ok y =>
      cases tail : xs.mapM decode with
      | error cause => simp [List.mapM_cons, head, tail, Bind.bind, Except.bind] at h
      | ok rest =>
        have same : y :: rest = ys := by
          simpa [List.mapM_cons, head, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst ys
        exact .cons head (ih tail)

private theorem decodePage_wire {limits : Limits} {bound : Bound}
    {dictionary : DictionaryChunk.Dictionary} {page : DictionaryChunk.DataPage}
    {ordinal : Nat} {slots : Slots} (decoded : decodePage limits bound dictionary page ordinal = .ok slots) :
    PageWire limits bound.snapshot.bytes dictionary page slots := by
  unfold decodePage at decoded
  split at decoded <;> try contradiction
  rename_i encoding
  refine ⟨not_not.mp encoding, ?_⟩
  cases read : DictionaryIndex.decode dictionary.entries page.params limits.scalar limits.indices
      (DictionaryChunk.body bound.snapshot.bytes page.frame) with
  | error cause => simp [read, Except.mapError] at decoded
  | ok values => simpa [read, Except.mapError] using decoded

private theorem count_wire {limits : Limits} {source : Bytes}
    {dictionary : DictionaryChunk.Dictionary} {data : List DictionaryChunk.DataPage}
    {pages : List Slots} (ordered : List.Forall₂ (PageWire limits source dictionary) data pages) :
    pages.flatten.length = (data.map (·.params.numValues)).sum := by
  induction ordered with
  | nil => rfl
  | cons head tail ih =>
    have count := (DictionaryIndex.decode_counts head.2).1
    simp [count, ih]

theorem readGroup_exact {limits : Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : Dictionary.readGroup limits bound index = .ok slots) :
    ∃ selected chunk dictionary header pages,
      selectChunk bound index = .ok selected ∧ frame limits bound selected = .ok chunk ∧
      chunk.span = selected.span ∧
      DictionaryChunk.Admitted limits bound.snapshot.bytes bound.snapshot.footer.start
        selected.group.numRows.toNat bound.field.layout selected.column.metadata chunk ∧
      Page.Chain selected.span selected.span.start selected.span.stop chunk.frames ∧
      (∀ page ∈ chunk.frames, Page.FrameWithin selected.span page.header.start page ∧
        (DictionaryChunk.body bound.snapshot.bytes page).length = page.value.compressedSize) ∧
      chunk.dictionary = some dictionary ∧ dictionary.frame.value.kind = .dictionary header ∧
      header.encoding = 0 ∧ dictionary.Exact limits bound.snapshot.bytes ∧
      List.Forall₂ (PageWire limits bound.snapshot.bytes dictionary) chunk.data pages ∧
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat := by
  cases selection : selectChunk bound index with
  | error cause => simp [Dictionary.readGroup, selection, Except.mapError, Bind.bind, Except.bind] at read
  | ok selected =>
    cases checked : frame limits bound selected with
    | error cause =>
      simp [Dictionary.readGroup, selection, checked, Except.mapError, Bind.bind, Except.bind] at read
    | ok chunk =>
      cases leading : chunk.dictionary with
      | none =>
        simp [Dictionary.readGroup, selection, checked, leading, Except.mapError, Bind.bind, Except.bind] at read
      | some dictionary =>
        cases kind : dictionary.frame.value.kind <;>
          simp [Dictionary.readGroup, selection, checked, leading, kind, Except.mapError, Bind.bind,
            Except.bind] at read
        rename_i header
        by_cases plain : header.encoding = 0
        · let decode := fun (entry : DictionaryChunk.DataPage × Nat) =>
            decodePage limits bound dictionary entry.1 entry.2
          cases decoded : (chunk.data.zipIdx 1).mapM decode with
          | error cause =>
            simp [plain, decode, decoded] at read
          | ok pages =>
            have values : pages.flatten = slots := by
              simpa [plain, decode, decoded, Bind.bind, Except.bind, Pure.pure, Except.pure] using read
            have zipped := (forAllMapM decode decoded).imp (fun _ _ h => decodePage_wire h)
            have ordered : List.Forall₂ (PageWire limits bound.snapshot.bytes dictionary) chunk.data pages := by
              have mapped := List.forall₂_map_left_iff.mpr zipped
              simpa using mapped
            have admitted := DictionaryChunk.read_admitted checked
            have span := Option.some.inj
              (admitted.interval.symm.trans (Date.Leaf.selectChunk_exact selection).2.2.2.2.1)
            have bounded := DictionaryChunk.read_payloads checked
            refine ⟨selected, chunk, dictionary, header, pages, rfl, checked, span, admitted, ?_, ?_,
              leading, kind, plain, admitted.dictionary _ leading, ordered, values.symm, ?_⟩
            · simpa [span] using (Page.readChunk_chain admitted.frames).2.2
            · simpa [span] using bounded
            · rw [← values, count_wire ordered, admitted.slots]
        · simp [plain] at read

theorem pageWire_exact {limits : Limits} {source : Bytes} {dictionary : DictionaryChunk.Dictionary}
    {page : DictionaryChunk.DataPage} {slots : Slots}
    (decoded : PageWire limits source dictionary page slots) :
    let body := DictionaryChunk.body source page.frame
    ∃ layout prepared width runs indices,
      ScalarPage.validateFor 8 page.params limits.scalar body = .ok layout ∧
      ScalarPage.PreparedWire page.params limits.scalar layout body prepared ∧
      prepared.scalars.toList = width :: runs ∧ width.toNat ≤ 32 ∧
      Hybrid.Wire width.toNat (prepared.mask.count true) runs indices ∧
      slots.map Option.isSome = prepared.mask ∧
      indices.map (fun index => dictionary.entries[index]?) = (slots.filterMap id).map some := by
  obtain ⟨_, prepared, refs, prep, indices, mask, ordered⟩ := DictionaryIndex.decode_ok_iff.mp decoded.2
  obtain ⟨layout, valid, exactBody⟩ := ScalarPage.prepareFor_sound prep
  obtain ⟨_, width, runs, octets, maxWidth, _, _, wire⟩ := DictionaryIndex.readIndices_ok_iff.mp indices
  exact ⟨layout, prepared, width, runs, refs, by rwa [← decoded.1], exactBody,
    octets, maxWidth, wire, mask, ordered⟩

end Silmaril.Proofs.Formats.Parquet.Date.Leaf.Dictionary
