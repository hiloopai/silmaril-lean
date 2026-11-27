module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Snappy.Defs
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Forall2
import Silmaril.Formats.Arrow.BinaryView.Stream.Thms
import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Thms
import Silmaril.Formats.Parquet.ByteArrayFallback.Thms
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Thms
import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.ByteArrayFallback.Snappy
open Silmaril.Formats.Arrow.BinaryView
open Footer.ColumnOrder (FlatLeaf field?)

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem checkUnannotated_wire {leaf : FlatLeaf} (checked : checkUnannotated leaf = .ok ()) :
    field? leaf.selection.leaf.item.fields 10 = .ok none ∧
    field? leaf.selection.leaf.item.fields 6 = .ok none := by
  unfold checkUnannotated at checked
  obtain ⟨logical, rawLogical, checked⟩ := bind_ok checked
  cases logical with
  | some => contradiction
  | none =>
    obtain ⟨converted, rawConverted, checked⟩ := bind_ok checked
    cases converted with
    | some => contradiction
    | none => exact ⟨mapError_ok rawLogical, mapError_ok rawConverted⟩

theorem openFile_wire {limits : ByteArrayFallback.Snappy.Limits} {input : Bytes} {name : String}
    {checked : Checked name} (opened : openFile limits input name = .ok checked) :
    File.openFile limits.file input name .optional = .ok checked.physical ∧
    ∃ selected, Footer.ColumnOrder.FlatWire limits.file.snapshot.footer checked.physical.snapshot
        checked.physical.binding.columnOrdinal selected ∧ selected.leaf = checked.physical.binding.leaf ∧
      field? selected.selection.leaf.item.fields 10 = .ok none ∧
      field? selected.selection.leaf.item.fields 6 = .ok none := by
  unfold openFile at opened
  obtain ⟨physical, admitted, opened⟩ := bind_ok opened
  split at opened <;> try contradiction
  rename_i selected bound
  split at opened <;> try contradiction
  rename_i annotation
  cases opened
  have original := Footer.ColumnOrder.readFlat_wire bound
  have sameLeaf := Option.some.inj (original.leafAt.symm.trans physical.binding.leafAt)
  exact ⟨mapError_ok admitted, selected, original, sameLeaf, checkUnannotated_wire annotation⟩

theorem readDictionary_wire {limits : ByteArrayFallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {frame : Page.Frame} {entries : Array Bytes}
    (read : readDictionary limits metadata source frame = .ok entries) :
    Utf8.Dictionary.Snappy.DictionaryBytesWire limits source frame entries.toList := by
  cases raw : Utf8.Dictionary.Snappy.readDictionaryBytes limits metadata source frame with
  | error cause => simp [readDictionary, raw, Except.map, Except.mapError] at read
  | ok values =>
    have same : values.toArray = entries := by simpa [readDictionary, raw, Except.map, Except.mapError] using read
    subst entries
    simpa using Utf8.Dictionary.Snappy.readDictionaryBytes_wire raw

theorem decodeData_wire {limits : ByteArrayFallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {dictionary : Option (Array Bytes)} {frame : Page.Frame} {slots : List (Option Bytes)}
    (read : decodeData limits metadata source dictionary frame = .ok slots) :
    ∃ entries, dictionary = some entries ∧ PageWire limits source entries frame slots := by
  cases dictionary with
  | none => contradiction
  | some entries =>
    simp only [decodeData] at read
    split at read <;> try contradiction
    · rename_i tag
      obtain ⟨original, bound, wire⟩ := Utf8.Dictionary.Snappy.decodeIndexPage_wire (mapError_ok read)
      cases bound
      exact ⟨entries, rfl, .inl ⟨tag, wire⟩⟩
    · rename_i tag
      exact ⟨entries, rfl, .inr ⟨tag, Utf8.Fallback.Snappy.decodePlainBytes_wire (mapError_ok read)⟩⟩

private theorem pages_count {limits : ByteArrayFallback.Snappy.Limits} {source : Bytes}
    {entries : Array Bytes} {frames : List Page.Frame} {pages : List (List (Option Bytes))}
    (ordered : List.Forall₂ (PageWire limits source entries) frames pages) :
    pages.flatten.length = (frames.map ByteArrayFallback.declaredSlots).sum := by
  induction ordered with
  | nil => rfl
  | cons wire _ ih =>
    have count := match wire with
    | .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    | .inr ⟨_, _, _, _, _, _, _, _, _, _, _, count⟩ => count
    simp [count, ih]

private theorem readFrames_wire {limits : ByteArrayFallback.Snappy.Limits} {metadata : Footer.ColumnMetadata}
    {source : Bytes} {group column rows : Nat} {name : String} {frames : List Page.Frame} {slots : List (Option Bytes)}
    (read : readFrames limits metadata source group column name rows frames = .ok slots) :
    FramesWire limits metadata source rows frames slots := by
  unfold readFrames at read
  obtain ⟨_, checked, read⟩ := bind_ok read
  have ⟨fits, size⟩ := Utf8.Dictionary.Snappy.checkExpandedChunk_wire checked
  refine ⟨fits, size, ?_⟩
  cases split : ByteArrayFallback.splitLeading frames with
  | mk leading originalData =>
    simp only [split] at read
    obtain ⟨_, phaseCheck, read⟩ := bind_ok read
    have schedule := Utf8.Fallback.checkPhasesWith_wire phaseCheck
    obtain ⟨dictionary, data, entries, pages, order, dictionaryAt, dataAt, count, opened, ordered, flatten⟩ :=
      ByteArrayFallback.readFramesWith_wire read
    cases dictionary with
    | none =>
      cases opened
      cases data with
      | nil => simp at dataAt
      | cons frame rest =>
        cases ordered with
        | cons first _ =>
          obtain ⟨_, impossible, _⟩ := decodeData_wire first
          contradiction
    | some frame =>
      obtain ⟨raw, parsed, opened⟩ := bind_ok opened
      cases opened
      have dictionaryWire := readDictionary_wire parsed
      have sameData : data = originalData := by
        obtain ⟨_, _, kind, _⟩ := dictionaryWire
        rw [order] at split
        simpa [ByteArrayFallback.splitLeading, kind] using congrArg Prod.snd split
      have pagesWire : List.Forall₂ (PageWire limits source raw) data pages :=
        ordered.imp (fun _ _ decoded => by
          obtain ⟨_, eq, wire⟩ := decodeData_wire decoded
          cases eq
          exact wire)
      exact ⟨frame, data, raw, pages, order, dictionaryAt.symm, dataAt, dictionaryWire,
        sameData.symm ▸ schedule, pagesWire, flatten, flatten ▸ (pages_count pagesWire).trans count⟩

theorem readGroup_wire {parquet : ByteArrayFallback.Snappy.Limits} {name : String} {checked : Checked name}
    {index : Nat} {slots : List (Option Bytes)} (read : readGroup parquet checked index = .ok slots) :
    ∃ group, GroupWire parquet checked index group slots := by
  obtain ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count,
    codec, located, framed, storedCap, decoded⟩ := ByteArrayFallback.readBoundGroupWithCodec_wire read
  have stored := Utf8.Dictionary.Snappy.storedBytes_exact located framed
  refine ⟨group, column, span, frames, leaf, groupAt, columnAt, path, physical, count, codec, located,
    framed, stored, ?_, readFrames_wire decoded⟩
  omega

theorem convert_readback {parquet : ByteArrayFallback.Snappy.Limits} {ipc : Arrow.Limits} {view : Column.Limits}
    {input : Bytes} {name : String} {wire : KBytes} (written : convert parquet ipc view input name = .ok wire) :
    ∃ (checked : Checked name) (groups : List (List (Option Bytes))) (batches : List (List (Option KBytes))),
      openFile parquet input name = .ok checked ∧
      List.Forall₂ (fun index slots => ∃ group, GroupWire parquet checked index group slots)
        (List.range checked.physical.snapshot.groupCount) groups ∧
      Stream.read ipc view wire = .ok ⟨⟨name, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) = groups.map (List.map (Option.map Bytes.toList)) ∧
      batches.map List.length = groups.map List.length ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchema ipc wire = .ok (⟨name, true, .binary⟩, start) ∧
        Stream.BatchesWire ipc view wire ⟨name, true, .binary⟩ ipc.batches start batches := by
  cases opened : openFile parquet input name with
  | error cause => simp [convert, opened, Except.mapError, Bind.bind, Except.bind] at written
  | ok checked =>
    cases read : (List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked) with
    | error cause => simp [convert, opened, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok groups =>
      let source : ToIpc.Source := ⟨⟨name, true⟩, groups⟩
      have emitted : StreamWriter.emit ipc view ⟨name, true, .binary⟩ source.batches = .ok wire := by
        cases h : StreamWriter.emit ipc view ⟨name, true, .binary⟩ source.batches <;>
          simp_all [convert, source, ToIpc.Source.ipcField, Except.mapError, Bind.bind, Except.bind]
      obtain ⟨batches, observed, values⟩ := StreamWriter.emit_binary_readback emitted
      have bytes := values.trans (ToIpc.batches_octets source)
      have counts : batches.map List.length = groups.map List.length := by
        simpa [source, List.map_map, Function.comp_def] using congrArg (List.map List.length) bytes
      exact ⟨checked, groups, batches, rfl, (List.mapM_eq_ok_iff_forall₂.mp read).imp (fun _ _ h => readGroup_wire h),
        observed, bytes, counts, (Stream.read_iff _ _ _ _).mp observed⟩

end Silmaril.Proofs.Formats.Parquet.ByteArrayFallback.Snappy
