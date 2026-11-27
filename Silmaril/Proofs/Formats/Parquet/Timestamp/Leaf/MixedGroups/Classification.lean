module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Snappy.Thms
import Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Thms
import Mathlib.Data.List.Forall2
import Batteries.Data.List.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Leaf (Bound Slots)
open Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary (DataPage CheckedChunk)
open Silmaril.Formats.Parquet.Timestamp.Leaf.MixedGroups

private theorem bind_ok {α β ε : Type} {input : Except ε α} {next : α → Except ε β} {out : β}
    (h : (input >>= next) = .ok out) : ∃ value, input = .ok value ∧ next value = .ok out := by
  cases input with
  | error => contradiction
  | ok value => exact ⟨value, rfl, h⟩

private theorem mapError_ok {α ε η : Type} {input : Except ε α} {wrap : ε → η} {out : α}
    (h : input.mapError wrap = .ok out) : input = .ok out := by
  cases input <;> cases h
  rfl

theorem route_policy (metadata : Footer.ColumnMetadata) (selected : Option DictionaryCodec) :
    route metadata = .ok selected ↔
      match selected with
      | none => metadata.dictionaryPageOffset = none ∧ (metadata.codec = 0 ∨ metadata.codec = 1)
      | some codec => metadata.dictionaryPageOffset.isSome = true ∧ metadata.codec = codec.id := by
  cases selected with
  | none =>
    cases offset : metadata.dictionaryPageOffset <;>
      by_cases zero : metadata.codec = 0 <;> by_cases one : metadata.codec = 1 <;>
      simp_all [route]
  | some codec =>
    cases codec <;> cases offset : metadata.dictionaryPageOffset <;>
      by_cases zero : metadata.codec = 0 <;> by_cases one : metadata.codec = 1 <;>
      simp_all [route, DictionaryCodec.id]

theorem checkSequence_wire {data : List DataPage} (admitted : checkSequence data = .ok ()) :
    (dictionaryLayout data).Wire data := by
  cases all : data.all Leaf.Fallback.isDictionary with
  | false =>
    simp only [checkSequence, DictionaryLayout.Wire, dictionaryLayout, all, Bool.false_eq_true, ↓reduceIte] at admitted ⊢
    exact Leaf.Fallback.checkSequence_wire admitted
  | true =>
    simp only [DictionaryLayout.Wire, dictionaryLayout, all, ↓reduceIte]
    constructor
    · intro empty
      simp [empty, checkSequence, dictionaryLayout] at admitted
    · intro page member
      simpa [Leaf.Fallback.isDictionary] using List.all_eq_true.mp all page member

private theorem planPlainPage_wire {bound : Bound} {codec : Int} {frame : Parquet.Page.Frame}
    {ordinal : Nat} {page : DataPage} (planned : planPlainPage bound codec frame ordinal = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels codec frame.value = .ok page.params ∧
      page.params.encoding = 0 := by
  unfold planPlainPage at planned
  obtain ⟨params, read, planned⟩ := bind_ok planned
  have parsed := mapError_ok read
  by_cases tag : params.encoding = 0
  · simp [tag, pure, Except.pure] at planned
    subst page
    exact ⟨rfl, parsed, tag⟩
  · simp [tag, Bind.bind, Except.bind] at planned

theorem planPlain_wire {limits : Leaf.Limits} {bound : Bound} {index : Nat} {chunk : Leaf.Chunk}
    {pages : List DataPage} (planned : planPlain limits bound index = .ok (.plain chunk pages)) :
    Leaf.selectChunk {limits with allowSnappy := true} bound index = .ok chunk ∧
      (chunk.column.metadata.codec = 0 ∨ chunk.column.metadata.codec = 1) ∧
      ∃ frames,
        Parquet.Page.readChunk limits.framing bound.snapshot.bytes chunk.span = .ok frames ∧
        Parquet.Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
        (frames.map Leaf.Internal.pageSlots).sum = chunk.group.numRows.toNat ∧
        List.Forall₂ (fun frame page =>
          page.frame = frame ∧ Timestamp.Page.parameters bound.binding.leaf bound.levels
            chunk.column.metadata.codec frame.value = .ok page.params ∧ page.params.encoding = 0)
          frames pages := by
  unfold planPlain at planned
  obtain ⟨selected, checked, planned⟩ := bind_ok planned
  obtain ⟨frames, framed, planned⟩ := bind_ok planned
  have wire := mapError_ok framed
  by_cases rows : (frames.map Leaf.Internal.pageSlots).sum = selected.group.numRows.toNat
  · simp only [rows, ne_eq, not_true_eq_false, ↓reduceIte, pure, Except.pure] at planned
    obtain ⟨data, plans, planned⟩ := bind_ok planned
    cases planned
    have codec := (Leaf.selectChunk_sound checked).2.2.2.2.2.1
    have known : chunk.column.metadata.codec = 0 ∨ chunk.column.metadata.codec = 1 := by
      simpa [Leaf.Limits.admitsCodec] using codec
    refine ⟨checked, known, frames, wire, (Parquet.Page.readChunk_chain wire).2.2, rows, ?_⟩
    rw [← List.zipIdx_map_fst 0 frames, List.forall₂_map_left_iff]
    exact (List.mapM_eq_ok_iff_forall₂.mp plans).imp fun _ _ read => planPlainPage_wire read
  · simp [rows, Bind.bind, Except.bind] at planned

private theorem planData_wire {codec : DictionaryCodec} {bound : Bound} {frame : Parquet.Page.Frame}
    {page : DataPage} (planned : planData codec bound frame = .ok page) :
    page.frame = frame ∧
      Timestamp.Page.parameters bound.binding.leaf bound.levels codec.id frame.value = .ok page.params ∧
      Leaf.Fallback.admits page.params.encoding = true := by
  cases codec with
  | uncompressed =>
    obtain ⟨same, _, _, wire, tag⟩ := Leaf.Dictionary.planDataWith_wire (admits := Leaf.Fallback.admits) planned
    exact ⟨same, wire, tag⟩
  | snappy => exact Leaf.Dictionary.Snappy.planDataWith_wire (admits := Leaf.Fallback.admits) planned

theorem planDictionary_wire {codec : DictionaryCodec} {limits : Leaf.Dictionary.Limits}
    {leafLimits : Leaf.Limits} {bound : Bound} {index : Nat} {layout : DictionaryLayout} {chunk : CheckedChunk}
    (planned : planDictionary codec limits leafLimits bound index = .ok (.dictionary codec layout chunk)) :
    Leaf.selectChunkWith codec.encoding leafLimits bound index = .ok chunk.chunk ∧
      chunk.chunk.column.metadata.codec = codec.id ∧
      chunk.chunk.span.stop - chunk.chunk.span.start ≤ limits.maxChunkBytes ∧
      Parquet.Page.readChunk leafLimits.framing bound.snapshot.bytes chunk.chunk.span = .ok chunk.frames ∧
      Parquet.Page.Chain chunk.chunk.span chunk.chunk.span.start chunk.chunk.span.stop chunk.frames ∧
      chunk.chunk.column.metadata.dictionaryPageOffset = some (chunk.dictionary.header.start : Int) ∧
      chunk.data.head?.map (fun page => (page.frame.header.start : Int)) =
        some chunk.chunk.column.metadata.dataPageOffset ∧
      readEntries codec limits leafLimits bound chunk.dictionary = .ok chunk.entries ∧
      (∀ page ∈ chunk.data,
        Timestamp.Page.parameters bound.binding.leaf bound.levels codec.id page.frame.value = .ok page.params ∧
        Leaf.Fallback.admits page.params.encoding = true) ∧
      (chunk.data.map (·.params.numValues)).sum = chunk.chunk.group.numRows.toNat ∧
      layout.Wire chunk.data := by
  unfold planDictionary at planned
  obtain ⟨checked, checkedRead, planned⟩ := bind_ok planned
  change Except.ok (Plan.dictionary codec (dictionaryLayout checked.data) checked) = _ at planned
  cases Except.ok.inj planned
  obtain ⟨chosen, cap, read, chain, dictionary, data, entries, plans, order, rows⟩ :=
    Leaf.Dictionary.checkGroupUsing_wire (fun success => (planData_wire success).1) checkedRead
  have admitted := (Leaf.selectChunkWith_sound chosen).2.2.2.2.2.1
  have actualCodec : chunk.chunk.column.metadata.codec = codec.id := by
    cases codec <;> simpa [DictionaryCodec.encoding, DictionaryCodec.id, Leaf.ChunkEncoding.admitsCodec] using admitted
  exact ⟨chosen, actualCodec, cap, read, chain, dictionary, data, entries,
    fun page member => (planData_wire (plans page member)).2, rows, checkSequence_wire order⟩

theorem planGroup_route {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {plan : Plan} (planned : planGroup limits leafLimits bound index = .ok plan) :
    ∃ group column selected, bound.snapshot.groupAt index = some group ∧
      group.columns[bound.ordinal - 1]? = some column ∧
      route column.metadata = .ok selected ∧
      match selected with
      | none => planPlain leafLimits bound index = .ok plan
      | some codec => planDictionary codec limits leafLimits bound index = .ok plan := by
  unfold planGroup at planned
  cases group : bound.snapshot.groupAt index with
  | none => simp [group] at planned
  | some actualGroup =>
    cases column : actualGroup.columns[bound.ordinal - 1]? with
    | none => simp [group, column] at planned
    | some actualColumn =>
      simp only [group, column] at planned
      obtain ⟨selected, picked, planned⟩ := bind_ok planned
      exact ⟨actualGroup, actualColumn, selected, rfl, column, picked, by cases selected <;> exact planned⟩

theorem planGroup_unknown_codec {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits} {bound : Bound}
    {index : Nat} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    (found : bound.snapshot.groupAt index = some group)
    (selected : group.columns[bound.ordinal - 1]? = some column)
    (notPlain : column.metadata.codec ≠ 0) (notSnappy : column.metadata.codec ≠ 1) :
    planGroup limits leafLimits bound index = .error (.chunkCodec column.metadata.codec) := by
  simp [planGroup, found, selected, route, notPlain, notSnappy, Bind.bind, Except.bind]

theorem readGroup_checked {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index : Nat} {slots : Slots bound} (read : readGroup limits leafLimits bound index = .ok slots) :
    ∃ plan, planGroup limits leafLimits bound index = .ok plan ∧
      decodePlan limits leafLimits bound plan = .ok slots :=
  bind_ok read

theorem readGroup_first_plain_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {chunk : Leaf.Chunk} {page : DataPage} {pages : List DataPage}
    {before after : List (DataPage × Nat)} {outputs : List (Slots bound)} {cause : Leaf.Error}
    (planned : planGroup limits leafLimits bound index = .ok (.plain chunk pages))
    (split : pages.zipIdx = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) => Leaf.Internal.decodeFrame leafLimits.page bound
      chunk.column.metadata.codec item.frame i) = .ok outputs)
    (failed : Leaf.Internal.decodeFrame leafLimits.page bound chunk.column.metadata.codec page.frame ordinal =
      .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, decodePlan, planned, split, earlier, failed, Bind.bind, Except.bind]

theorem readGroup_first_dictionary_page_error {limits : Leaf.Dictionary.Limits} {leafLimits : Leaf.Limits}
    {bound : Bound} {index ordinal : Nat} {codec : DictionaryCodec} {layout : DictionaryLayout}
    {chunk : CheckedChunk} {page : DataPage} {before after : List (DataPage × Nat)}
    {outputs : List (List (Option Int64))} {cause : Leaf.Error}
    (planned : planGroup limits leafLimits bound index = .ok (.dictionary codec layout chunk))
    (split : chunk.data.zipIdx 1 = before ++ (page, ordinal) :: after)
    (earlier : before.mapM (fun (item, i) =>
      decodeDictionaryPage codec layout limits leafLimits bound chunk.entries.toArray item i) = .ok outputs)
    (failed : decodeDictionaryPage codec layout limits leafLimits bound chunk.entries.toArray page ordinal =
      .error cause) :
    readGroup limits leafLimits bound index = .error cause := by
  simp [readGroup, decodePlan, planned, split, earlier, failed, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.Timestamp.Leaf.MixedGroups
