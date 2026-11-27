module

public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk.Chain

@[expose] public section

namespace Silmaril.Formats.Parquet.RecursiveSchema.Chunk

theorem admitPageWith_wire {requireEqualSizes : Bool} {frame : Page.Frame} {remaining : Nat}
    {info : Page.DataV1} (read : admitPageWith requireEqualSizes frame remaining = .ok info) :
    frame.value.kind = .dataV1 info ∧
      (info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
      info.numValues ≤ remaining ∧
      (requireEqualSizes = true → frame.value.uncompressedSize = frame.value.compressedSize) :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.admit_with_wire read

theorem admitPage_wire {frame : Page.Frame} {remaining : Nat} {info : Page.DataV1}
    (read : admitPage frame remaining = .ok info) : HeaderWire frame remaining info :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.admit_wire read

theorem definitions_wire {leaf : Leaf} {limits : Hybrid.Limits} {count : Nat} {body : Bytes}
    {definitions : Definitions} (read : readDefinitions leaf limits count body = .ok definitions) :
    DefinitionWire leaf limits count body definitions ∧ definitions.levels.length = count :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.definitions_wire read

/-- Every resulting slot comes from the original classified level and each
original signed word goes to the corresponding present slot in order. -/
theorem decodePage_wire {limits : Limits} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {firstRow remaining : Nat} {slots : List Slot}
    (read : decodePage limits leaf source frame firstRow remaining = .ok slots) :
    PageWire limits leaf source frame firstRow remaining slots :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.decodePage_wire read

theorem ChainWire.originalFrames {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    Page.Chain carrier.span start.byte stop.byte (pages.map ObservedPage.frame) :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.chain_frames wire

theorem ChainWire.rowCount {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    start.row + (pages.flatMap ObservedPage.slots).length = stop.row :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.chain_rows wire

/-- A successful chunk covers its original span with consecutive frames
and returns precisely the checked footer group's slot count. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : ChunkBinding schema group column} {output : Observation}
    (accepted : Chunk.read limits binding = .ok output) :
    Wire limits binding output :=
  Proofs.Formats.Parquet.RecursiveSchema.Chunk.read_wire accepted

end Silmaril.Formats.Parquet.RecursiveSchema.Chunk
