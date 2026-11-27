module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Formats.Parquet.DictionaryIndex.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.V2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Leaf)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

public theorem readDictionary_wire {limits : Limits} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {dictionary : Dictionary}
    (read : readDictionary limits leaf source frame = .ok dictionary) :
    dictionary.frame = frame ∧ DictionaryWire limits leaf source dictionary := by
  unfold readDictionary at read
  split at read
  · rename_i info kind
    split at read
    · contradiction
    · rename_i encoding
      split at read
      · contradiction
      · rename_i entries
        split at read
        · contradiction
        · rename_i bytes
          split at read
          · contradiction
          · rename_i sizes
            obtain ⟨body, bodyRead, read⟩ := bind_ok read
            obtain ⟨words, wordRead, done⟩ := bind_ok read
            obtain ⟨_, original, exact, count, width, ordered⟩ :=
              Plain.decodeFixedWidth_ok_iff.mp (from_mapError wordRead)
            cases Except.ok.inj done
            exact ⟨rfl, ⟨info, body, original, kind, Classical.not_not.mp encoding,
              Nat.le_of_not_gt entries, Nat.le_of_not_gt bytes,
              readV1Body_wire (fun _ => Classical.not_not.mp sizes) bodyRead,
              exact, count, width, congrArg List.toArray ordered⟩⟩
  · contradiction

public theorem decodeDictionarySlots_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {reps defs : List Nat} {suffix : Bytes} {start : State} {rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDictionarySlots limits leaf dictionary reps defs suffix start rowCeiling = .ok decoded) :
    DictionarySlotsWire limits leaf dictionary reps defs suffix start rowCeiling decoded := by
  unfold decodeDictionarySlots at read
  obtain ⟨classified, levelRead, read⟩ := bind_ok read
  obtain ⟨indices, indexRead, read⟩ := bind_ok read
  obtain ⟨words, selected, read⟩ := bind_ok read
  obtain ⟨aligned, alignment, done⟩ := bind_ok read
  have selection := from_mapError selected
  obtain ⟨byteCap, width, runs, exact, widthCap, runCap, countCap, hybrid⟩ :=
    DictionaryIndex.readIndices_ok_iff.mp (from_mapError indexRead)
  obtain ⟨mask, positions⟩ := FlatPage.reconstruct_ok_iff.mp (from_mapError alignment)
  cases Except.ok.inj done
  exact ⟨classifySlots_wire levelRead, mask, width, runs, indices, exact, widthCap, byteCap,
    countCap, runCap, hybrid, fun _ member => DictionaryIndex.select_indices_lt selection member,
    (DictionaryIndex.select_ok_iff.mp selection).trans (congrArg (List.map some) positions.symm)⟩

public theorem decodeDictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDictionaryPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded := by
  unfold decodeDictionaryPage at read
  obtain ⟨info, header, read⟩ := bind_ok read
  obtain ⟨body, decodedBody, read⟩ := bind_ok read
  obtain ⟨reps, repRead, read⟩ := bind_ok read
  obtain ⟨defs, defRead, read⟩ := bind_ok read
  obtain ⟨kind, encodings, cap, sizes⟩ := RecursiveSchema.Chunk.admitPageWith_wire (from_mapError header)
  obtain ⟨repetition, repCount⟩ := levels_wire (from_mapError repRead)
  obtain ⟨definition, _⟩ := levels_wire (from_mapError defRead)
  have decodedWire := decodeDictionarySlots_wire read
  have count : decoded.levels.length = info.numValues := by
    simpa only [List.length_map, repCount] using congrArg List.length (original_levels decodedWire.slots).1
  exact ⟨info, body, reps, defs, kind, encodings, cap, readV1Body_wire sizes decodedBody,
    repetition, definition, decodedWire, count⟩

public theorem dictionaryPage_counts {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded) :
    start.slot + decoded.levels.length = decoded.after.slot ∧
      start.rows + decoded.levels.countP LevelSlot.startsRow = decoded.after.rows := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, slots, _⟩ := wire.original
  exact slot_counts slots.slots

private theorem identity_v2 (info : Page.DataV2) : ColumnCodec.uncompressed.v2 info = 0 := by
  cases flag : info.isCompressed <;>
    simp [ColumnCodec.v2, ScalarPage.v2Codec, ColumnCodec.id, ColumnCodec.payload, Payload.Codec.id, flag]

public theorem decodeV2DictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV2DictionaryPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded := by
  unfold decodeV2DictionaryPage at read
  obtain ⟨info, header, read⟩ := bind_ok read
  obtain ⟨sections, sectionsRead, read⟩ := bind_ok read
  obtain ⟨suffix, suffixRead, read⟩ := bind_ok read
  obtain ⟨kind, encoding, cap, sizes⟩ := admitV2Page_wire header
  have sameSizes := sizes (identity_v2 info)
  have sectionsWire := readV2Sections_wire sectionsRead
  obtain ⟨storedExtent, _, suffixWire⟩ := readV2Suffix_wire suffixRead
  cases suffixWire with
  | compressed _ nonzero _ _ _ _ _ => exact False.elim (nonzero (identity_v2 info))
  | raw _ suffixSize =>
    obtain ⟨first, rows, nulls, checked, indices, closed⟩ := checkV2Slots_wire read
    have slotWire := decodeDictionarySlots_wire indices
    have count := congrArg List.length (original_levels slotWire.slots).1
    simp only [List.length_map, sectionsWire.count] at count
    exact ⟨info, sections, checked, kind, encoding, cap, sameSizes, storedExtent, sectionsWire,
      suffixSize, first, rows, nulls, closed ▸ count, slotWire, closed⟩

public theorem v2Dictionary_accounting {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded) :
    ∃ info, frame.value.kind = .dataV2 info ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP LevelSlot.startsRow = info.numRows ∧
      absentSlots decoded = info.numNulls ∧ decoded.after.live = false := by
  obtain ⟨info, sections, checked, kind, _, _, _, _, _, _, _, rows, nulls, count, slots, closed⟩ := wire.original
  subst decoded
  change checked.levels.length = info.numValues at count
  have aligned : checked.words.length = info.numValues := by
    simpa only [List.length_map, count] using congrArg List.length slots.aligned
  have rowCount : checked.levels.countP LevelSlot.startsRow = info.numRows := by
    rw [← rows, ← (original_levels slots.slots).1]
    simp only [List.count_eq_countP, List.countP_map]
    rfl
  exact ⟨info, kind, count, aligned, rowCount, nulls, rfl⟩

public theorem decodeDictionaryDataPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDictionaryDataPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded := by
  unfold decodeDictionaryDataPage at read
  split at read
  · exact .v1 (decodeDictionaryPage_wire read)
  · exact .v2 (decodeV2DictionaryPage_wire read)
  · contradiction

public theorem dictionaryDataPage_counts {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded) :
    start.slot + decoded.levels.length = decoded.after.slot ∧
      start.rows + decoded.levels.countP LevelSlot.startsRow = decoded.after.rows := by
  cases wire with
  | v1 original => exact dictionaryPage_counts original
  | v2 original =>
    obtain ⟨_, _, checked, _, _, _, _, _, _, _, _, _, _, _, slots, closed⟩ := original.original
    subst decoded
    simpa only [closeV2] using slot_counts slots.slots

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk
