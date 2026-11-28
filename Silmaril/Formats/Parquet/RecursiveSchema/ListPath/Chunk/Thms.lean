module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Levels
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Chain

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk

public section

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
    (binding.span.start : Int) = binding.column.metadata.dataPageOffset ∧
      (binding.span.stop : Int) = binding.column.metadata.dataPageOffset +
        binding.column.metadata.totalCompressedSize ∧
      binding.span.start < binding.span.stop ∧ binding.span.stop ≤ snapshot.footer.start :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.binding_span binding

theorem step_wire {plan : Plan} {wrappers : List Nat} {ceiling : Nat} {start stop : State}
    {rep defn : Nat} (accepted : step plan wrappers ceiling start rep defn = .ok stop) :
    StepWire plan wrappers ceiling start rep defn stop :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.step_wire accepted

theorem decodePage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec}
    (accepted : decodePage limits plan wrappers source frame start remaining ceiling codec = .ok decoded) :
    PageWire limits plan wrappers source frame start remaining ceiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodePage_wire accepted

theorem decodeV2Page_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec}
    (accepted : decodeV2Page limits plan wrappers source frame start remaining ceiling codec = .ok decoded) :
    V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodeV2Page_wire accepted

theorem decodeDataPage_wire {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec}
    (accepted : decodeDataPage limits plan wrappers source frame start remaining ceiling codec = .ok decoded) :
    DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.decodeDataPage_wire accepted

/-- An original V2 header separately accounts for slots, row starts and
null markers. Its outgoing cursor has no live repeated wrapper. -/
theorem V2PageWire.counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec) :
    ∃ info, frame.value.kind = .dataV2 info ∧ decoded.atoms.length = info.numValues ∧
      decoded.atoms.countP (·.repetition == 0) = info.numRows ∧ absentSlots decoded = info.numNulls ∧
      decoded.after.live = 0 ∧ start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.v2_page_counts wire

theorem PageWire.counts {limits : Limits} {plan : Plan} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} (wire : PageWire limits plan wrappers source frame start remaining ceiling decoded codec) :
    ∃ info, frame.value.kind = .dataV1 info ∧ decoded.atoms.length = info.numValues ∧
      start.slots + decoded.atoms.length = decoded.after.slots ∧
      start.rows + decoded.atoms.countP (·.repetition == 0) = decoded.after.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.page_counts wire

theorem ChainWire.counts {limits : Limits} {carrier : Carrier} {start stop : State} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start stop pages) :
    start.slots + (pages.flatMap (·.decoded.atoms)).length = stop.slots ∧
    start.rows + (pages.flatMap (·.decoded.atoms)).countP (·.repetition == 0) = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.chain_counts wire

theorem Wire.originalHeader {limits : Limits} {carrier : Carrier} {output : Observation} {frame : Page.Frame}
    (wire : Wire limits carrier output) (member : frame ∈ output.frames) :
    Page.readPage limits.framing carrier.source carrier.span frame.header.start = .ok frame :=
  Page.readChunk_readPage wire.framed frame member

theorem read_page_failure {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {address : RecursiveSchema.Chunk.Address} {ordinal byte : Nat}
    {start : State} {cause : PageCause}
    (refused : read limits binding = .error (.page address ordinal byte start cause)) :
    PageFailureWire limits (carrierOf binding) address ordinal byte start cause :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.read_page_failure refused

theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {out : Observation} (accepted : read limits binding = .ok out) :
    Wire limits (carrierOf binding) out :=
  Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.read_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk
