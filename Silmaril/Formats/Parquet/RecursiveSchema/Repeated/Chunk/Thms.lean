module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.V2
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Chain
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Dictionary

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

@[expose] public section

theorem readLevels_wire {limits : Hybrid.Limits} {maximum count : Nat} {body : Bytes}
    {result : LevelBlock} (read : readLevels limits maximum count body = .ok result) :
    LevelWire limits maximum count body result ∧ result.levels.length = count :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.levels_wire read

theorem classifySlots_wire {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {out : Classified}
    (accepted : classifySlots leaf ceiling reps defs start = .ok out) :
    SlotsWire leaf ceiling reps defs start out.levels out.after :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.classifySlots_wire accepted

theorem SlotsWire.original_levels {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List LevelSlot}
    (wire : SlotsWire leaf ceiling reps defs start slots stop) :
    slots.map (·.repetition) = reps ∧ slots.map (·.definition) = defs :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.original_levels wire

theorem SlotsWire.counts {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List LevelSlot}
    (wire : SlotsWire leaf ceiling reps defs start slots stop) :
    start.slot + slots.length = stop.slot ∧
      start.rows + slots.countP LevelSlot.startsRow = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.slot_counts wire

/-- A locally valid continuation still requires a previously reached element
slot on the same path, including at a page boundary. -/
theorem rejects_closed_continuation {leaf : Leaf} {ceiling rep defn : Nat}
    {reps defs : List Nat} {start : State} {slot : Repeated.Slot}
    (classified : leaf.classify start.slot rep defn = .ok slot)
    (continuation : rep ≠ 0) (closed : start.live = false) :
    classifySlots leaf ceiling (rep :: reps) (defn :: defs) start =
      .error (.continuationWithoutList start.slot) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.rejects_closed_continuation
    classified continuation closed

/-- V1 binds the stored frame and its CRC to the bounded decoded body
before interpreting the two serialized level sections and signed suffix. -/
theorem decodeV1Page_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV1Page limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    PageWire limits leaf source frame start remaining rowCeiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeV1Page_wire read

theorem decodePage_wire {limits : Limits} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodePage limits leaf source frame start remaining rowCeiling = .ok decoded) :
    PageWire limits leaf source frame start remaining rowCeiling decoded :=
  decodeV1Page_wire read

theorem PageWire.counts {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : PageWire limits leaf source frame start remaining rowCeiling decoded codec) :
    start.slot + decoded.levels.length = decoded.after.slot ∧
      start.rows + decoded.levels.countP LevelSlot.startsRow = decoded.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.v1_state_counts wire

theorem readV2Levels_wire {limits : Hybrid.Limits} {maximum count : Nat} {bytes : Bytes}
    {levels : List Nat} (read : readV2Levels limits maximum count bytes = .ok levels) :
    V2LevelWire limits maximum count bytes levels ∧ levels.length = count :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.v2_levels_wire read

/-- The original value suffix is used raw or expands by the selected checked
payload relation, after both header subtractions are shown in bounds. -/
theorem readV2Suffix_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf}
    {frame : Page.Frame} {info : Page.DataV2} {stored raw : Bytes}
    (read : readV2Suffix limits codec leaf frame info stored = .ok raw) :
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
      V2SuffixWire limits codec frame info stored raw :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV2Suffix_wire read

/-- The V2 header, stored-body checksum, original spans and codec witness
bind the exact classified slots to the decoded signed suffix. -/
theorem decodeV2Page_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV2Page limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    V2PageWire limits codec leaf source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeV2Page_wire read

/-- The decoded suffix contains one full signed word per non-null slot.
The output cursor is closed at the V2 row boundary. -/
theorem V2PageWire.accounting {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : V2PageWire limits codec leaf source frame start remaining rowCeiling decoded) :
    ∃ info spans suffix, frame.value.kind = .dataV2 info ∧ frame.v2Spans = some spans ∧
      V2SuffixWire limits codec frame info (bytesAt source spans.values) suffix ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP LevelSlot.startsRow = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      suffix.length = (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth leaf.kind ∧
      decoded.after.live = false :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.v2_accounting wire

theorem decodeDataPage_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDataPage limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    DataPageWire limits codec leaf source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeDataPage_wire read

/-- The ordered entries come from exact signed words in the original
checksum-checked dictionary frame. -/
theorem readDictionary_wire {limits : Limits} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {dictionary : Dictionary}
    (read : readDictionary limits leaf source frame = .ok dictionary) :
    dictionary.frame = frame ∧ DictionaryWire limits leaf source dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readDictionary_wire read

/-- Every present slot follows the exact original padded Hybrid stream and
selects an in-range word from this chunk's dictionary in original order. -/
theorem decodeDictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDictionaryPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeDictionaryPage_wire read

/-- The V2 raw sections, exact Hybrid suffix and local dictionary bind the
original slots and values. The V2 cursor closes even for an empty page. -/
theorem decodeV2DictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV2DictionaryPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeV2DictionaryPage_wire read

theorem V2DictionaryPageWire.accounting {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded) :
    ∃ info, frame.value.kind = .dataV2 info ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP LevelSlot.startsRow = info.numRows ∧
      absentSlots decoded = info.numNulls ∧ decoded.after.live = false :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.v2Dictionary_accounting wire

/-- Within a dictionary-first chunk, the original per-page tag binds
either exact PLAIN words or indices into the same leading dictionary. -/
theorem decodeDictionaryDataPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeDictionaryDataPage limits leaf dictionary source frame start remaining rowCeiling = .ok decoded) :
    DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeDictionaryDataPage_wire read

theorem readPrefix_wire {limits : Limits} {carrier : Carrier}
    {metadata : Footer.ColumnMetadata} {encoding : FramedEncoding metadata}
    {dictionary : Option Dictionary} (read : readPrefix limits carrier metadata encoding = .ok dictionary) :
    PrefixAdmission limits carrier metadata dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readPrefix_wire read

/-- The strict lower-level walk covers the supplied carrier span and
attains its exact counts, including when writing before footer construction. -/
theorem walk_empty_prefix_wire {limits : Limits} {carrier : Carrier} {budget : Nat}
    {cursor : Cursor} {pages : List ObservedPage}
    (read : walk limits carrier budget cursor [] = .ok pages) :
    ∃ stop, pages.length ≤ budget ∧ stop.byte = carrier.span.stop ∧
      stop.state.slot = carrier.slots ∧ stop.state.rows = carrier.rows ∧
      ChainWire limits carrier cursor stop pages :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.walk_empty_prefix_wire read

theorem ChainWire.originalFrames {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    Page.Chain carrier.span start.byte stop.byte (pages.map ObservedPage.frame) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.chain_frames wire

theorem ChainWire.counts {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    start.page + pages.length = stop.page ∧
    start.state.slot + (Observation.mk pages none).levels.length = stop.state.slot ∧
    start.state.rows + (Observation.mk pages none).levels.countP LevelSlot.startsRow = stop.state.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.chain_counts wire

/-- Starting with no live list, successful decoding walks consecutive
original pages when framed and attains both independent original footer counts. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    (accepted : read limits binding = .ok output) : Wire limits binding output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.read_wire accepted

/-- A checked pageless column carries no page and cannot designate a positive
source byte range, even when neighboring columns have framed bodies. -/
theorem Wire.noSpan {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    (wire : Wire limits binding output) (empty : binding.span? = none) :
    output.pages = [] ∧ Page.columnSpan snapshot.footer.start binding.chunk.metadata = none :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.noSpan_wire wire empty

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
