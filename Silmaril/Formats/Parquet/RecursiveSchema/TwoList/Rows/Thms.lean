module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Projection
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.Read

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows

open Arrow.RecursiveSchema.Batch.Rows (Observation Row RowFits)

public section

/-- A source-free projection fixes both the logical Arrow declaration
and the order of the signed leaves. -/
theorem Relation.typedWords {plan : Plan} {input : List Atom} {rows : List Row}
    (relation : Relation plan input rows) :
    (∀ row ∈ rows, RowFits (arrowSchema plan).fields row) ∧
      rows.flatMap rowWords = input.filterMap Atom.word :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.relation_sound relation

/-- The checked levels and aligned words have the same extent. Every atom
keeps its original repetition, definition and optional signed word. -/
theorem decoded_axes {limits : Chunk.Limits} {encoding : Chunk.ValueEncoding} {plan : Plan} {ceiling : Nat} {start : Chunk.State} {reps defs : List Nat}
    {suffix : Silmaril.Formats.Bytes} {decoded : Chunk.Decoded}
    (wire : Chunk.DecodedWire limits plan ceiling start reps defs suffix decoded encoding) :
    (pageAtoms decoded).map Atom.repetition = reps ∧
    (pageAtoms decoded).map Atom.definition = defs ∧
    (pageAtoms decoded).map Atom.word = decoded.words :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.decoded_axes wire

theorem chain_trace_rows {limits : Chunk.Limits} {carrier : Chunk.Carrier} {start stop : Chunk.State}
    {frames : List Page.Frame} {pages : List Chunk.ObservedPage}
    {dictionary : Option Repeated.Chunk.Dictionary}
    (wire : Chunk.ChainWire limits carrier dictionary start frames pages stop) :
    start.rows + (atoms pages).countP (fun slot => slot.repetition == 0) = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.chain_trace_rows wire

/-- Every checked split of the same ordered trace yields the same batch
result. The trace also determines the row count for both splits. -/
theorem reconstructObservation_reframe {plan : Plan} {before after : Chunk.Observation}
    {leftLimits rightLimits : Chunk.Limits} {left right : Chunk.Carrier}
    (first : Chunk.Wire leftLimits left before) (second : Chunk.Wire rightLimits right after)
    (same : atoms before.pages = atoms after.pages) :
    reconstructObservation plan before = reconstructObservation plan after :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.reframe first second same

theorem reconstruct_wire {plan : Plan} {expected : Nat} {input : List Atom} {out : Observation}
    (accepted : reconstruct plan expected input = .ok out) :
    ObservationWire plan input expected out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.reconstruct_wire accepted

/-- The original positional column and its wire proof supply the trace
and group count for the Arrow batch witness. -/
theorem readGroup_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {group : Nat} {out : Observation}
    (accepted : readGroup limits schema group = .ok out) : GroupWire limits schema group out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.group_wire accepted

theorem readAll_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {limits : Chunk.Limits} {schema : Compiled schemaLimits snapshot} {out : List Observation}
    (accepted : readAll limits schema = .ok out) :
    List.Forall₂ (GroupWire limits schema) (List.range snapshot.groupCount) out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Rows.read_all_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows
