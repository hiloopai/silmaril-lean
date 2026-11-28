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

theorem readV1Body_wire {limits : Limits} {codec : ColumnCodec} {source : Bytes}
    {frame : Page.Frame} {body : Bytes}
    (sizes : (codec == ColumnCodec.uncompressed) = true →
      frame.value.uncompressedSize = frame.value.compressedSize)
    (read : readV1Body limits codec source frame = .ok body) :
    V1BodyWire limits codec source frame body :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV1Body_wire sizes read

theorem admitV2Page_wire {codec : ColumnCodec} {frame : Page.Frame} {remaining : Nat}
    {encoding : Int} {info : Page.DataV2}
    (read : admitV2Page codec frame remaining encoding = .ok info) :
    frame.value.kind = .dataV2 info ∧ info.encoding = encoding ∧ info.numValues ≤ remaining ∧
      (codec.v2 info = 0 → frame.value.uncompressedSize = frame.value.compressedSize) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.admitV2Page_wire read

theorem checkV2Counts_wire {α ε : Type} {info : Page.DataV2} {reps : List Nat}
    {slot : Nat} {report : PageCause → ε} {absent : α → Nat} {decode : Unit → Except ε α} {decoded : α}
    (accepted : checkV2Counts info reps slot report absent decode = .ok decoded) :
    reps.head?.getD 0 = 0 ∧ reps.count 0 = info.numRows ∧ absent decoded = info.numNulls ∧
      decode () = .ok decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.checkV2Counts_wire accepted

theorem readV2SectionsWith_wire {limits : RecursiveSchema.Chunk.Limits}
    {maxRepetition maxDefinition : Nat} {source : Bytes}
    {frame : Page.Frame} {info : Page.DataV2} {sections : V2Sections}
    (read : readV2SectionsWith limits maxRepetition maxDefinition source frame info = .ok sections) :
    V2SectionsWireWith limits maxRepetition maxDefinition source frame info sections :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV2SectionsWith_wire read

theorem chain_storedSize {span : Footer.Span} {start stop : Nat} {frames : List Page.Frame}
    (wire : Page.Chain span start stop frames) : stop = start + storedChunkBytes frames :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.chain_storedSize wire

theorem readV2SuffixWith_wire {limits : Limits} {codec : ColumnCodec}
    {frame : Page.Frame} {info : Page.DataV2} {stored raw : Bytes} {signedExtent : Option Nat}
    (read : readV2SuffixWith limits codec frame info stored signedExtent = .ok raw) :
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
      V2SuffixWire limits codec frame info stored raw :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readV2SuffixWith_wire read

/-- A false V2 flag has only the raw wire constructor. -/
theorem V2SuffixWire.eq_of_false {limits : Limits} {codec : ColumnCodec}
    {frame : Page.Frame} {info : Page.DataV2} {stored raw : Bytes}
    (wire : V2SuffixWire limits codec frame info stored raw) (flag : info.isCompressed = false) :
    raw = stored := by
  cases wire with
  | raw => rfl
  | compressed enabled => simp [flag] at enabled

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

/-- A dictionary codec selects the same original column codec as the full
table, for every codec admitted in the dictionary-first profile. -/
theorem DictionaryCodec.column_ofId {id : Int} {codec : DictionaryCodec}
    (read : DictionaryCodec.ofId id = some codec) : ColumnCodec.ofId id = some codec.column := by
  unfold DictionaryCodec.ofId at read
  split at read <;> simp_all [ColumnCodec.ofId, DictionaryCodec.column] <;> cases read <;> rfl

theorem PrefixWire.matchesBinding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat} {binding : Binding schema group column}
    {limits : Limits} {span : Footer.Span} {dictionary : Dictionary}
    (wire : PrefixWire limits (carrierOf binding span) binding.chunk.metadata dictionary) :
    dictionary.codec.column = binding.codec :=
  Option.some.inj ((DictionaryCodec.column_ofId wire.codec).symm.trans binding.originalCodec)

/-- The ordered entries come from exact signed words in the original
checksum-checked dictionary frame. -/
theorem readDictionaryWith_wire {limits : Limits} {kind : RecursiveSchema.Kind} {source : Bytes}
    {frame : Page.Frame} {dictionary : Dictionary} {codec : DictionaryCodec}
    (read : readDictionaryWith limits kind source frame codec = .ok dictionary) :
    dictionary.frame = frame ∧ dictionary.codec = codec ∧ DictionaryContentsWire limits kind source dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readDictionaryWith_wire read

theorem readFramedDictionary_wire {limits : Limits} {kind : RecursiveSchema.Kind}
    {source : Bytes} {span : Footer.Span} {metadata : Footer.ColumnMetadata} {frames rest : List Page.Frame}
    {codec : DictionaryCodec} {table : Dictionary}
    (read : readFramedDictionary limits kind source span metadata frames codec = .ok (table, rest)) :
    FramedDictionaryWire limits kind source span metadata frames codec table rest :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readFramedDictionary_wire read

theorem readDictionary_wire {limits : Limits} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {dictionary : Dictionary} {codec : DictionaryCodec}
    (read : readDictionary limits leaf source frame codec = .ok dictionary) :
    dictionary.frame = frame ∧ dictionary.codec = codec ∧ DictionaryWire limits leaf source dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.readDictionary_wire read

/-- Every present slot follows the exact original padded Hybrid stream and
selects an in-range word from this chunk's dictionary in original order. -/
theorem decodeDictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage} {codec : DictionaryCodec}
    (read : decodeDictionaryPage limits leaf dictionary source frame start remaining rowCeiling codec = .ok decoded) :
    DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeDictionaryPage_wire read

/-- The V2 raw sections, exact Hybrid suffix and local dictionary bind the
original slots and values. The V2 cursor closes even for an empty page. -/
theorem decodeV2DictionaryPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage} {codec : DictionaryCodec}
    (read : decodeV2DictionaryPage limits leaf dictionary source frame start remaining rowCeiling codec = .ok decoded) :
    V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodeV2DictionaryPage_wire read

theorem V2DictionaryPageWire.accounting {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage} {codec : DictionaryCodec}
    (wire : V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec) :
    ∃ info, frame.value.kind = .dataV2 info ∧
      decoded.levels.length = info.numValues ∧ decoded.words.length = info.numValues ∧
      decoded.levels.countP LevelSlot.startsRow = info.numRows ∧
      absentSlots decoded = info.numNulls ∧ decoded.after.live = false :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.v2Dictionary_accounting wire

/-- Within a dictionary-first chunk, the original per-page tag binds
either exact PLAIN words or indices into the same leading dictionary. -/
theorem decodeDictionaryDataPage_wire {limits : Limits} {leaf : Leaf} {dictionary : Array Word}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage} {codec : DictionaryCodec}
    (read : decodeDictionaryDataPage limits leaf dictionary source frame start remaining rowCeiling codec = .ok decoded) :
    DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec :=
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

/-- Both original footer byte totals include every original frame header
and the dictionary's stored or decoded body, respectively. -/
theorem Wire.chunkBytes {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation} {span : Footer.Span}
    (wire : Wire limits binding output) (framed : binding.span? = some span) :
    binding.chunk.metadata.totalCompressedSize = Int.ofNat (storedChunkBytes output.frames) ∧
      binding.chunk.metadata.totalUncompressedSize = Int.ofNat (rawChunkBytes output.frames) :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.chunkBytes_wire wire framed

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
