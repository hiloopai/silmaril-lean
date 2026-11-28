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

private theorem decodeFrames_wire {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {ordinal : Nat} {state : State} {reversed : List ObservedPage} {out : Observation}
    (accepted : decodeFrames limits carrier frames ordinal state reversed = .ok out) :
    ∃ pages, out.pages = reversed.reverse ++ pages ∧ ChainWire limits carrier state frames pages out.stop := by
  induction frames generalizing ordinal state reversed out with
  | nil =>
    cases Except.ok.inj accepted
    exact ⟨[], by simp, .nil state⟩
  | cons frame frames ih =>
    simp only [decodeFrames] at accepted
    obtain ⟨decoded, first, rest⟩ := bind_ok accepted
    obtain ⟨pages, eq, wire⟩ := ih rest
    refine ⟨⟨frame, state, decoded⟩ :: pages, ?_, .cons (decodeDataPage_wire (from_mapError first)) wire⟩
    simpa [List.reverse_cons, List.append_assoc] using eq

private theorem chain_frames {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
    pages.map ObservedPage.frame = frames := by
  induction wire <;> simp_all

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
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
        · rename_i raw
          obtain ⟨frames, scan, accepted⟩ := bind_ok accepted
          obtain ⟨decoded, bodyRead, accepted⟩ := bind_ok accepted
          split at accepted
          · contradiction
          · rename_i slots
            split at accepted
            · contradiction
            · rename_i rows
              cases Except.ok.inj accepted
              obtain ⟨_, eq, wire⟩ := decodeFrames_wire bodyRead
              simp only [List.reverse_nil, List.nil_append] at eq
              rw [← eq] at wire
              have framesEq := chain_frames wire
              have scanExact := framesEq.symm ▸ from_mapError scan
              exact ⟨scanExact, (Page.readChunk_chain scanExact).2.2, framesEq.symm ▸ wire,
                Decidable.not_not.mp raw, Decidable.not_not.mp slots, Decidable.not_not.mp rows,
                Nat.le_of_not_gt chunkCap, Nat.le_of_not_gt slotCap, Nat.le_of_not_gt rowCap⟩

private theorem equal_extents {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
    RecursiveSchema.Repeated.Chunk.rawChunkBytes frames = RecursiveSchema.Repeated.Chunk.storedChunkBytes frames := by
  induction wire with
  | nil => rfl
  | @cons _ frame _ _ _ _ page _ ih =>
    have sizes : frame.value.uncompressedSize = frame.value.compressedSize := by
      cases page with
      | v1 first =>
        obtain ⟨_, _, _, _, _, header, _⟩ := first.original
        exact header.sizes
      | v2 second =>
        obtain ⟨_, _, _, _, _, _, sizes, _⟩ := second.original
        exact sizes
    simp only [RecursiveSchema.Repeated.Chunk.rawChunkBytes, RecursiveSchema.Repeated.Chunk.storedChunkBytes, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [sizes, ih]

public theorem chunk_bytes {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation} (wire : Wire limits (carrierOf binding) out) :
    let frames := out.pages.map ObservedPage.frame
    (binding.span.start : Int) = binding.column.metadata.dataPageOffset ∧
    binding.column.metadata.totalCompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.storedChunkBytes frames) ∧
    binding.column.metadata.totalUncompressedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.rawChunkBytes frames) := by
  have framed := binding.originalSpan
  simp only [Page.columnSpan, binding.offsets.1, Option.getD_none] at framed
  obtain ⟨offset, total, _⟩ := Footer.checkDataSpan_some_iff.mp framed
  have extent := RecursiveSchema.Repeated.Chunk.chain_storedSize wire.original
  have same := equal_extents wire.decoded
  have raw := wire.uncompressed
  change binding.column.metadata.totalUncompressedSize = Int.ofNat (binding.span.stop - binding.span.start) at raw
  change binding.span.stop = binding.span.start + _ at extent
  have bytes : binding.span.stop - binding.span.start =
      RecursiveSchema.Repeated.Chunk.storedChunkBytes (out.pages.map ObservedPage.frame) := by omega
  refine ⟨offset, ?_, raw.trans (congrArg Int.ofNat (bytes.trans same.symm))⟩
  change _ = (RecursiveSchema.Repeated.Chunk.storedChunkBytes (out.pages.map ObservedPage.frame) : Int)
  omega

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk
