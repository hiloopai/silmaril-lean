module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Levels
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Chain
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Omitted

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk

public section

variable {P : Type} [ScanShape P]

theorem Codec.column_ofId {id : Int} {codec : Codec} (read : Codec.ofId id = some codec) :
    Repeated.Chunk.ColumnCodec.ofId id = some codec.column := by
  unfold Codec.ofId at read
  split at read <;> simp_all [Repeated.Chunk.ColumnCodec.ofId, Codec.column] <;> cases read <;> rfl

theorem Binding.codec_exact {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    Repeated.Chunk.ColumnCodec.ofId binding.column.metadata.codec = some binding.codec.column :=
  Codec.column_ofId binding.originalCodec

theorem Binding.span_exact {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    let offset := binding.column.metadata.dictionaryPageOffset.getD binding.column.metadata.dataPageOffset
    (binding.span.start : Int) = offset ∧
      (binding.span.stop : Int) = offset +
        binding.column.metadata.totalCompressedSize ∧
      binding.span.start < binding.span.stop ∧ binding.span.stop ≤ snapshot.footer.start :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.binding_span binding

theorem step_wire {plan : P} {wrappers : List Nat} {ceiling : Nat} {start stop : State}
    {rep defn : Nat} (accepted : step plan wrappers ceiling start rep defn = .ok stop) :
    StepWire plan wrappers ceiling start rep defn stop :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.step_wire accepted

theorem decodePage_wire {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodePage limits plan wrappers source frame start remaining ceiling codec encoding = .ok decoded) :
    PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodePage_wire accepted

theorem decodeV2Page_wire {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (accepted : decodeV2Page limits plan wrappers source frame start remaining ceiling codec encoding = .ok decoded) :
    V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodeV2Page_wire accepted

theorem decodeDataPage_wire {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {dictionary : Option Repeated.Chunk.Dictionary}
    (accepted : decodeDataPage limits plan wrappers source frame start remaining ceiling codec dictionary = .ok decoded) :
    DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodeDataPage_wire accepted

/-- An original V2 header separately accounts for slots, row starts and
null markers. Its outgoing cursor has no live repeated wrapper. -/
theorem V2PageWire.counts {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding) :
    ∃ info, frame.value.kind = .dataV2 info ∧ decoded.atoms.length = info.numValues ∧
      decoded.atoms.countP (·.repetition == 0) = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      decoded.after.live = 0 ∧ start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.v2_page_counts wire

theorem PageWire.counts {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding) :
    ∃ info, frame.value.kind = .dataV1 info ∧ decoded.atoms.length = info.numValues ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.page_counts wire

/-- An omitted V1 repetition section consumes no bytes and synthesizes one zero per slot. -/
theorem SectionsWire.zero_repetition {limits : Hybrid.Limits} {plan : P} {count : Nat} {input : SectionSource}
    {spans : Sections} {reps defs : List Nat} {suffix : Bytes}
    (wire : SectionsWire limits plan count input spans reps defs suffix)
    (zero : (ScanShape.shape plan).repetitions = 0) :
    spans.repetition.start = spans.repetition.stop ∧ reps = List.replicate count 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.section_zero_repetition wire zero

/-- An omitted V1 definition section consumes no bytes and synthesizes one zero per slot. -/
theorem SectionsWire.zero_definition {limits : Hybrid.Limits} {plan : P} {count : Nat} {input : SectionSource}
    {spans : Sections} {reps defs : List Nat} {suffix : Bytes}
    (wire : SectionsWire limits plan count input spans reps defs suffix)
    (zero : (ScanShape.shape plan).definitions = 0) :
    spans.definition.start = spans.definition.stop ∧ defs = List.replicate count 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.section_zero_definition wire zero

/-- A V2 page at repetition width zero has zero stored repetition bytes and one row per slot. -/
theorem V2PageWire.zero_repetition {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding)
    (zero : (ScanShape.shape plan).repetitions = 0) :
    ∃ info, frame.value.kind = .dataV2 info ∧ info.repetitionBytes = 0 ∧ info.numRows = info.numValues :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.v2_zero_repetition wire zero

/-- A V2 page at definition width zero has zero stored definition bytes and zero null slots. -/
theorem V2PageWire.zero_definition {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding)
    (zero : (ScanShape.shape plan).definitions = 0) :
    ∃ info, frame.value.kind = .dataV2 info ∧ info.definitionBytes = 0 ∧ info.numNulls = 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.v2_zero_definition wire zero

theorem ChainWire.counts {limits : Limits} {carrier : Carrier P} {start stop : State} {pages : List ObservedPage}
    {dictionary : Option Repeated.Chunk.Dictionary}
    (wire : ChainWire limits carrier dictionary start stop pages) :
    start.slots + (pages.flatMap (·.decoded.atoms)).length = stop.slots ∧
    start.rows + (pages.flatMap (·.decoded.atoms)).countP (·.repetition == 0) = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.chain_counts wire

theorem Wire.originalHeader {limits : Limits} {carrier : Carrier P} {output : Observation} {frame : Page.Frame}
    (wire : Wire limits carrier output) (member : frame ∈ output.frames) :
    Page.readPage limits.framing carrier.source carrier.span frame.header.start = .ok frame :=
  Page.readChunk_readPage wire.framed frame member

theorem Wire.dictionary_anchors {limits : Limits} {carrier : Carrier P} {observed : Observation}
    {table : Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier observed) (found : observed.dictionary = some table) :
    ∃ first,
      (observed.pages.map ObservedPage.frame).head? = some first ∧
      Page.readPage limits.framing carrier.source carrier.span carrier.span.start = .ok table.frame ∧
      table.frame.header.start = carrier.span.start ∧
      first.header.start = table.frame.payload.stop ∧
      carrier.metadata.dictionaryPageOffset = some (Int.ofNat table.frame.header.start) ∧
      carrier.metadata.dataPageOffset = Int.ofNat first.header.start :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.dictionary_anchors wire found

/-- The original column codec and checked dictionary agree for any carrier. -/
theorem Wire.dictionary_payloadOf {limits : Limits} {carrier : Carrier P}
    {observed : Observation} {table : Repeated.Chunk.Dictionary}
    (wire : Wire limits carrier observed)
    (codec : Repeated.Chunk.ColumnCodec.ofId carrier.metadata.codec = some carrier.codec.column)
    (found : observed.dictionary = some table) :
    Repeated.Chunk.DictionaryCodec.ofId carrier.metadata.codec = some table.codec ∧
      table.codec.column = carrier.codec.column ∧
      Repeated.Chunk.DictionaryContentsWire limits.payload (ScanShape.shape carrier.plan).leaf.2 carrier.source table :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.dictionary_payload codec wire found

/-- The checked dictionary uses the same original column codec as its data
pages. Its wire witness covers the stored CRC, decoded extent and signed entries. -/
theorem Wire.dictionary_payload {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {observed : Observation} {table : Repeated.Chunk.Dictionary}
    (wire : Wire limits (carrierOf binding) observed) (found : observed.dictionary = some table) :
    Repeated.Chunk.DictionaryCodec.ofId binding.column.metadata.codec = some table.codec ∧
      table.codec.column = binding.codec.column ∧
      Repeated.Chunk.DictionaryContentsWire limits.payload schema.plan.shape.leaf.2 snapshot.bytes table :=
  wire.dictionary_payloadOf binding.codec_exact found

theorem ChainWire.page_of_mem {limits : Limits} {carrier : Carrier P} {dictionary : Option RecursiveSchema.Repeated.Chunk.Dictionary}
    {start stop : State} {pages : List ObservedPage} {page : ObservedPage}
    (chain : ChainWire limits carrier dictionary start stop pages) (member : page ∈ pages) :
    DataPageWire limits carrier.plan (wrappers carrier.plan) carrier.source page.frame page.start
      (carrier.slots - page.start.slots) carrier.rows page.decoded carrier.codec dictionary :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.chain_page_of_mem chain member

/-- Refusals from the shared original frame and payload reader with no
extra frame restriction retain the original addressed prefix. -/
theorem readCarrier_page_failure {limits : Limits} {carrier : Carrier P}
    {encoding : ColumnEncoding carrier.metadata} {address : RecursiveSchema.Chunk.Address}
    {ordinal byte : Nat} {start : State} {cause : PageCause}
    (refused : readCarrier limits carrier encoding (fun _ => .ok ()) = .error (.page address ordinal byte start cause)) :
    PageFailureWire limits carrier address ordinal byte start cause :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.readCarrier_page_failure refused

theorem read_page_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {start : State} {cause : PageCause}
    (refused : read limits binding = .error (.page address ordinal byte start cause)) :
    PageFailureWire limits (carrierOf binding) address ordinal byte start cause :=
  readCarrier_page_failure refused

theorem readCarrier_dictionary_failure {limits : Limits} {carrier : Carrier P}
    {encoding : ColumnEncoding carrier.metadata} {address : RecursiveSchema.Chunk.Address}
    {ordinal byte : Nat} {cause : Repeated.Chunk.PageCause}
    (refused : readCarrier limits carrier encoding (fun _ => .ok ()) = .error (.dictionary address ordinal byte cause)) :
    DictionaryFailureWire limits carrier encoding address ordinal byte cause :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.readCarrier_dictionary_failure refused

theorem read_dictionary_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {cause : Repeated.Chunk.PageCause}
    (refused : read limits binding = .error (.dictionary address ordinal byte cause)) :
    DictionaryFailureWire limits (carrierOf binding) binding.encodings address ordinal byte cause :=
  readCarrier_dictionary_failure refused

theorem readCarrier_wire {limits : Limits} {carrier : Carrier P} {encoding : ColumnEncoding carrier.metadata}
    {checkFrames : List Page.Frame → Except Error Unit} {out : Observation}
    (accepted : readCarrier limits carrier encoding checkFrames = .ok out) :
    Wire limits carrier out ∧ checkFrames out.frames = .ok () :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.readCarrier_wire accepted

theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {out : Observation} (accepted : read limits binding = .ok out) :
    Wire limits (carrierOf binding) out :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.read_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk
