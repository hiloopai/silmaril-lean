module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.V2
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList
open Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

private theorem readPrefix_wire {limits : Limits} {carrier : Carrier}
    {encoding : ColumnEncoding carrier.metadata} {frames : List Page.Frame}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary} {data : List Page.Frame}
    (accepted : readPrefix limits carrier encoding frames = .ok (dictionary, data)) :
    PrefixWire limits carrier dictionary frames data := by
  cases encoding with
  | plain _ offset =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj accepted)
    exact .plain offset
  | dictionary _ =>
    unfold readPrefix at accepted
    dsimp only at accepted
    split at accepted
    · rename_i offset offsetEq
      split at accepted
      · contradiction
      · rename_i original
        split at accepted
        · rename_i frame tail splitFrames
          obtain ⟨checked, checkedRead, result⟩ := bind_ok accepted
          split at result
          · contradiction
          · rename_i anchors
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
            obtain ⟨rfl, codec, words⟩ :=
              RecursiveSchema.Repeated.Chunk.readDictionaryWith_wire (from_mapError checkedRead)
            exact .dictionary codec
              (offsetEq.trans (congrArg some (Classical.not_not.mp original))) (by omega) (by omega) words
        · contradiction
    · contradiction

private theorem decodeFrames_wire {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {ordinal : Nat} {state : State}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary} {reversed : List ObservedPage} {out : Observation}
    (accepted : decodeFrames limits carrier dictionary frames ordinal state reversed = .ok out) :
    ∃ pages, out.pages = reversed.reverse ++ pages ∧ out.dictionary = dictionary ∧
      ChainWire limits carrier dictionary state frames pages out.stop := by
  induction frames generalizing ordinal state reversed out with
  | nil =>
    cases Except.ok.inj accepted
    exact ⟨[], by simp, rfl, .nil state⟩
  | cons frame frames ih =>
    simp only [decodeFrames] at accepted
    obtain ⟨decoded, first, rest⟩ := bind_ok accepted
    obtain ⟨pages, eq, sameDictionary, wire⟩ := ih rest
    refine ⟨⟨frame, state, decoded⟩ :: pages, ?_, sameDictionary, .cons (decodeDataPage_wire (from_mapError first)) wire⟩
    simpa [List.reverse_cons, List.append_assoc] using eq

private theorem chain_frames {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : ChainWire limits carrier dictionary start frames pages stop) :
    pages.map ObservedPage.frame = frames := by
  induction wire <;> simp_all

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : ChainWire limits carrier dictionary start frames pages stop) :
    start.slots + (pages.flatMap (·.decoded.levels)).length = stop.slots ∧
      start.rows + (pages.flatMap (·.decoded.levels)).countP Slot.startsRow = stop.rows := by
  induction wire with
  | nil => simp
  | cons first _ ih =>
    obtain ⟨slots, rows⟩ := page_counts first
    obtain ⟨tailSlots, tailRows⟩ := ih
    simp only [List.flatMap_cons, List.length_append, List.countP_append]
    omega

public theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation}
    (accepted : RecursiveSchema.TwoList.Chunk.read limits binding = .ok out) : Wire limits (carrierOf binding) out := by
  unfold RecursiveSchema.TwoList.Chunk.read at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i chunkCap
    split at accepted
    · contradiction
    · rename_i slotCap
      split at accepted
      · contradiction
      · rename_i rowCap
        split at accepted
        · contradiction
        · rename_i earlyExtent
          obtain ⟨frames, scan, accepted⟩ := bind_ok accepted
          obtain ⟨⟨dictionary, data⟩, leadingRead, accepted⟩ := bind_ok accepted
          obtain ⟨decoded, bodyRead, accepted⟩ := bind_ok accepted
          split at accepted
          · contradiction
          · rename_i slots
            split at accepted
            · contradiction
            · rename_i rows
              split at accepted
              · contradiction
              · rename_i rawBytes
                cases Except.ok.inj accepted
                obtain ⟨_, eq, sameDictionary, wire⟩ := decodeFrames_wire bodyRead
                simp only [List.reverse_nil, List.nil_append] at eq
                rw [← eq] at wire
                have framesEq := chain_frames wire
                have leading := readPrefix_wire leadingRead
                have complete : out.frames = frames := by
                  unfold Observation.frames
                  rw [sameDictionary, framesEq]
                  cases leading <;> rfl
                have scanExact := complete.symm ▸ from_mapError scan
                refine ⟨scanExact, (Page.readChunk_chain scanExact).2.2, ?_, ?_,
                  Decidable.not_not.mp rawBytes, Decidable.not_not.mp slots, Decidable.not_not.mp rows,
                  Nat.le_of_not_gt chunkCap, Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩
                · rw [sameDictionary, framesEq, complete]
                  exact leading
                · rw [sameDictionary, framesEq]
                  exact wire

public theorem codec_matches {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    (carrierOf binding).codec.column.id = binding.column.metadata.codec := by
  change binding.codec.column.id = binding.column.metadata.codec
  have selected := binding.originalCodec
  unfold Codec.ofId at selected
  split at selected <;> first
  | contradiction
  | rename_i id
    rw [← Option.some.inj selected, id]
    rfl

public theorem chunk_bytes {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation} (wire : Wire limits (carrierOf binding) out) :
    let frames := out.frames
    (binding.span.start : Int) = binding.column.metadata.dictionaryPageOffset.getD binding.column.metadata.dataPageOffset ∧
    binding.column.metadata.totalCompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.storedChunkBytes frames) ∧
    binding.column.metadata.totalUncompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.rawChunkBytes frames) := by
  have framed := binding.originalSpan
  unfold Page.columnSpan at framed
  obtain ⟨offset, total, _⟩ := Footer.checkDataSpan_some_iff.mp framed
  have extent := RecursiveSchema.Repeated.Chunk.chain_storedSize wire.original
  refine ⟨offset, ?_, wire.uncompressed⟩
  change binding.span.stop = binding.span.start + _ at extent
  change _ = (RecursiveSchema.Repeated.Chunk.storedChunkBytes out.frames : Int)
  omega

private theorem first_header {span : Footer.Span} {start stop : Nat} {frame : Page.Frame}
    {frames : List Page.Frame} (chain : Page.Chain span start stop (frame :: frames)) :
    frame.header.start = start := by
  cases chain with
  | cons within _ => exact within.headerStart

private theorem prefix_details {limits : Limits} {carrier : Carrier}
    {dictionary : RecursiveSchema.Repeated.Chunk.Dictionary} {frames data : List Page.Frame}
    (leading : PrefixWire limits carrier (some dictionary) frames data) :
    dictionary.codec.column = carrier.codec.column ∧
    carrier.metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start) ∧
    carrier.metadata.dataPageOffset = Int.ofNat dictionary.frame.payload.stop ∧
    dictionary.frame.payload.stop < carrier.span.stop ∧
    RecursiveSchema.Repeated.Chunk.DictionaryContentsWire limits.payload carrier.plan.kind carrier.source dictionary := by
  cases leading with
  | dictionary codec offset data hasData words =>
    exact ⟨congrArg RecursiveSchema.Repeated.Chunk.DictionaryCodec.column codec, offset, data, hasData, words⟩

public theorem dictionary_anchors {limits : Limits} {carrier : Carrier} {out : Observation}
    {dictionary : RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier out) (selected : out.dictionary = some dictionary) :
    dictionary.codec.column = carrier.codec.column ∧
    carrier.metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start) ∧
    carrier.metadata.dataPageOffset = Int.ofNat dictionary.frame.payload.stop ∧
    Page.readPage limits.framing carrier.source carrier.span carrier.span.start = .ok dictionary.frame ∧
    RecursiveSchema.Repeated.Chunk.DictionaryContentsWire limits.payload carrier.plan.kind carrier.source dictionary := by
  have member : dictionary.frame ∈ out.frames := by simp [Observation.frames, selected]
  have page := Page.readChunk_readPage wire.origFrames dictionary.frame member
  have first : dictionary.frame.header.start = carrier.span.start := by
    have chain := wire.original
    rw [show out.frames = dictionary.frame :: out.pages.map ObservedPage.frame by simp [Observation.frames, selected]] at chain
    exact first_header chain
  have leading := wire.leading
  rw [selected] at leading
  obtain ⟨codec, offset, data, _, contents⟩ := prefix_details leading
  exact ⟨codec, offset, data, first ▸ page, contents⟩

private theorem following_header {span : Footer.Span} {start stop : Nat} {first : Page.Frame}
    {frames : List Page.Frame} (chain : Page.Chain span start stop (first :: frames))
    (hasData : first.payload.stop < stop) :
    ∃ next, frames.head? = some next ∧ next.header.start = first.payload.stop := by
  cases chain with
  | cons _ rest =>
    cases rest with
    | nil => omega
    | cons next _ => exact ⟨_, rfl, next.headerStart⟩

public theorem dictionary_first_data {limits : Limits} {carrier : Carrier} {out : Observation}
    {dictionary : RecursiveSchema.Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier out) (selected : out.dictionary = some dictionary) :
    ∃ page, out.pages.head? = some page ∧
      carrier.metadata.dataPageOffset = Int.ofNat page.frame.header.start := by
  have leading := wire.leading
  rw [selected] at leading
  obtain ⟨_, _, offset, hasData, _⟩ := prefix_details leading
  have chain := wire.original
  rw [show out.frames = dictionary.frame :: out.pages.map ObservedPage.frame by simp [Observation.frames, selected]] at chain
  obtain ⟨frame, head, after⟩ := following_header chain hasData
  cases pages : out.pages with
  | nil => simp [pages] at head
  | cons page rest =>
    have same : page.frame = frame := by simpa [pages] using head
    exact ⟨page, rfl, by rw [offset, same, after]⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
