module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback
open Silmaril.Formats.Arrow.MixedFlat

private theorem forM_member {α ε : Type} {check : α → Except ε PUnit} {items : List α}
    (passed : items.forM check = .ok ⟨⟩) {item : α} (member : item ∈ items) : check item = .ok ⟨⟩ := by
  induction items with
  | nil => simp at member
  | cons head tail ih =>
    change forM (head :: tail) check = .ok ⟨⟩ at passed
    rw [List.forM_cons] at passed
    cases tested : check head with
    | error cause => simp [tested, Bind.bind, Except.bind] at passed
    | ok value =>
      cases value
      rw [List.mem_cons] at member
      rcases member with rfl | member
      · exact tested
      · exact ih (by simpa [tested, Bind.bind, Except.bind] using passed) member

private theorem checkPlainTag_ok {ε : Type} {dictionaryAfterPlain : ε}
    {group column ordinal : Nat} {name : String} {frame : Page.Frame}
    (passed : checkPlainTagWith dictionaryAfterPlain group column name ordinal frame = .ok ⟨⟩) : dataEncoding frame = some 0 := by
  unfold checkPlainTagWith at passed
  split at passed <;> first | contradiction | assumption

theorem checkPhasesWith_wire {ε : Type} {dictionaryAfterPlain : ε}
    {group column firstOrdinal : Nat} {name : String} {data : List Page.Frame}
    (passed : checkPhasesWith dictionaryAfterPlain group column name firstOrdinal data = .ok ⟨⟩) : Phases data := by
  unfold checkPhasesWith at passed
  dsimp only at passed
  split at passed <;> try contradiction
  rename_i both
  simp only [Bool.or_eq_true, List.isEmpty_iff, not_or] at both
  refine ⟨data.takeWhile isDictionaryData, data.dropWhile isDictionaryData,
    List.takeWhile_append_dropWhile.symm, both.1, both.2, ?_, ?_⟩
  · intro frame member
    simpa [isDictionaryData] using (List.all_eq_true.mp List.all_takeWhile) frame member
  · intro frame member
    rw [← List.zipIdx_map_fst (firstOrdinal + (data.takeWhile isDictionaryData).length)
      (data.dropWhile isDictionaryData)] at member
    obtain ⟨⟨original, ordinal⟩, inside, same⟩ := List.mem_map.mp member
    cases same
    exact checkPlainTag_ok (forM_member passed inside)

private theorem decodePlain_wire {limits : Utf8.Fallback.Limits} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {frame : Page.Frame} {slots : List (Option String)}
    (read : decodePlain limits leaf metadata source frame = .ok slots) : PlainPageWire limits metadata source frame slots := by
  unfold decodePlain at read
  cases bounded : ByteArrayFallback.bodyLimits limits.file.column.maxPageBytes frame.value with
  | error cause => simp [bounded, Except.mapError, Bind.bind, Except.bind] at read
  | ok _ =>
    simp only [bounded, Except.mapError, Bind.bind, Except.bind] at read
    split at read <;> try contradiction
    cases physical : File.decodePage limits.file .optional leaf metadata frame.value
        (FlatColumn.frameBody source frame) with
    | error cause => simp [physical] at read
    | ok raw =>
      cases strict : Utf8.decodeSlotsWith DecodeError.invalidPlainText raw with
      | error cause => simp [physical, strict] at read
      | ok text =>
        have same : text = slots := by simpa [physical, strict] using read
        subst text
        have bytes : slots.map (Option.map Utf8.Dictionary.octets) = raw := Utf8.decodeSlotsWith_exact strict
        have wire := File.decodePage_wire physical
        have length : raw.length = ByteArrayFallback.declaredSlots frame := by
          obtain ⟨params, _, _, _, original, _, _, _, _, count, _⟩ := wire
          unfold ByteArrayFallback.declaredSlots
          cases kind : frame.value.kind <;>
            simp [FlatColumn.pageParameters, kind] at original ⊢ <;>
            subst params <;> exact count
        exact ⟨by simpa [← bytes] using length, by simpa [bytes] using wire⟩

theorem decodeData_wire {limits : Utf8.Fallback.Limits} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {dictionary : Option (Array String)}
    {frame : Page.Frame} {slots : List (Option String)}
    (read : decodeData limits leaf metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits metadata source entries frame slots := by
  cases dictionary with
  | none => contradiction
  | some entries =>
    simp only [decodeData] at read
    split at read <;> try contradiction
    · rename_i tag
      cases decoded : Utf8.Dictionary.decodePage limits metadata source (some entries) frame with
      | error cause => simp [decoded, Except.mapError] at read
      | ok text =>
        have same : text = slots := by simpa [decoded, Except.mapError] using read
        subst text
        obtain ⟨original, bound, wire⟩ := Utf8.Dictionary.decodePage_wire decoded
        cases bound
        exact ⟨entries, rfl, .inl ⟨tag, wire⟩⟩
    · rename_i tag
      exact ⟨entries, rfl, .inr ⟨tag, decodePlain_wire read⟩⟩

private theorem pages_count {limits : Utf8.Fallback.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {entries : Array String} {frames : List Page.Frame} {pages : List (List (Option String))}
    (ordered : List.Forall₂ (PageWire limits metadata source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    have count := match wire with
    | .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    | .inr ⟨_, count, _⟩ => count
    simp [count, ih]

private theorem readFrames_wire {limits : Utf8.Fallback.Limits} {leaf : Footer.SchemaElement}
    {metadata : Footer.ColumnMetadata} {source : Bytes} {group column rows : Nat} {name : String}
    {frames : List Page.Frame} {slots : List (Option String)}
    (read : readFrames limits leaf metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold readFrames at read
  cases split : ByteArrayFallback.splitLeading frames with
  | mk leading originalData =>
    rw [split] at read
    simp only [Bind.bind, Except.bind] at read
    cases checked : checkPhases group column name (if leading.isSome = true then 1 else 0) originalData with
    | error cause => rw [checked] at read; contradiction
    | ok value =>
      cases value
      have schedule := checkPhasesWith_wire checked
      rw [checked] at read
      obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, opened, ordered, flatten⟩ :=
        ByteArrayFallback.readFramesWith_wire read
      cases dictionary with
      | none =>
        cases opened
        cases data with
        | nil => simp at dataAt
        | cons frame rest =>
          cases ordered with
          | cons first _ => obtain ⟨_, impossible, _⟩ := decodeData_wire first; contradiction
      | some frame =>
        cases typed : Utf8.Dictionary.readDictionary limits metadata source frame with
        | error cause => simp [Option.mapM, typed, Except.mapError] at opened
        | ok text =>
          have same : entries = some text := by
            simpa [Option.mapM, typed, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] using opened.symm
          subst entries
          have dictWire := Utf8.Dictionary.readDictionary_wire typed
          obtain ⟨header, _, kind, _⟩ := dictWire
          have dataIsOriginal : data = originalData := by
            rw [order] at split
            simpa [ByteArrayFallback.splitLeading, kind] using congrArg Prod.snd split
          have pagesWire : List.Forall₂ (PageWire limits metadata source text) data pages :=
            ordered.imp (fun _ _ decoded => by
              obtain ⟨_, eq, wire⟩ := decodeData_wire decoded
              cases eq
              exact wire)
          exact ⟨frame, data, text, pages, order, dictionaryAt.symm, dataAt, Utf8.Dictionary.readDictionary_wire typed,
            dataIsOriginal.symm ▸ schedule, pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : Utf8.Fallback.Limits} {name : String} {checked : Checked name} {index : Nat}
    {slots : List (Option String)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, decoded⟩ := ByteArrayFallback.readBoundGroupWith_wire read
  exact ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, readFrames_wire decoded⟩

theorem convert_readback {parquet : Utf8.Fallback.Limits} {ipc : Arrow.MixedFlat.Limits} {input : Bytes} {name : String}
    {wire : KBytes} (written : convert parquet ipc input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option String))) (decoded : Stream.Observed),
      Utf8.Dictionary.openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc wire = .ok decoded ∧ decoded.fields = Utf8.fields name .optional ∧
      decoded.batches.map StreamWriter.observeBatch = groups.map (fun slots =>
        (slots.length, some [(⟨name, true, .view .utf8⟩, .utf8View slots)])) ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame ipc.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire ipc wire decoded.fields ipc.observation.ipc.batches 0 start decoded.batches := by
  cases opened : Utf8.Dictionary.openFile parquet input name with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases read : (List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked) with
    | error cause => simp [convert, opened, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      have emitted : OrderedWriter.emit ipc (Utf8.fields name .optional)
          (groups.map (Utf8.batch name .optional)) = .ok wire := by
        cases h : OrderedWriter.emit ipc (Utf8.fields name .optional) (groups.map (Utf8.batch name .optional)) <;>
          simp_all [convert, Except.mapError, Bind.bind, Except.bind]
      obtain ⟨decoded, observed, schema, values, framing⟩ := OrderedWriter.emit_readback emitted
      refine ⟨checked, groups, decoded, rfl, (List.mapM_eq_ok_iff_forall₂.mp read).imp
        (fun _ _ group => readGroup_wire group), observed, schema, ?_, framing⟩
      simpa [List.map_map, Function.comp_def, Utf8.batch, OrderedWriter.BatchInput.observe,
        OrderedWriter.Column.field, OrderedWriter.Column.observe] using values

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.Fallback
