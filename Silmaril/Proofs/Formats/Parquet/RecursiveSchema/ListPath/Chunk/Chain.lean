module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Footer.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Page

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath
open Parquet.RecursiveSchema.ListPath.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {out : β}
    (read : (first >>= next) = .ok out) : ∃ found, first = .ok found ∧ next found = .ok out := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {out : α}
    (read : first.mapError wrap = .ok out) : first = .ok out := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

public theorem binding_span {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) :
    (binding.span.start : Int) = binding.column.metadata.dataPageOffset ∧
      (binding.span.stop : Int) = binding.column.metadata.dataPageOffset +
        binding.column.metadata.totalCompressedSize ∧
      binding.span.start < binding.span.stop ∧ binding.span.stop ≤ snapshot.footer.start := by
  have fromFooter := Footer.checkDataSpan_some_iff.mp
    (by simpa [Page.columnSpan, binding.offsets.1] using binding.originalSpan :
      Footer.checkDataSpan snapshot.footer.start binding.column.metadata.dataPageOffset
        binding.column.metadata.totalCompressedSize = some binding.span)
  exact ⟨fromFooter.1, fromFooter.2.1, fromFooter.2.2.2.1, fromFooter.2.2.2.2⟩

private theorem decodeFrames_wire {limits : Limits} {carrier : Carrier} {frames : List Page.Frame}
    {ordinal : Nat} {start : State} {reversed : List ObservedPage} {out : Observation}
    (accepted : decodeFrames limits carrier (wrappers carrier.plan) frames ordinal start reversed = .ok out) :
    ∃ suffix, out.pages = reversed.reverse ++ suffix ∧ suffix.map ObservedPage.frame = frames ∧
      ChainWire limits carrier start out.stop suffix := by
  induction frames generalizing ordinal start reversed out with
  | nil =>
    cases Except.ok.inj accepted
    exact ⟨[], by simp, rfl, .nil _⟩
  | cons frame frames ih =>
    simp only [decodeFrames] at accepted
    obtain ⟨decoded, page, rest⟩ := bind_ok accepted
    obtain ⟨suffix, final, original, chain⟩ := ih rest
    exact ⟨⟨frame, start, decoded⟩ :: suffix, by simpa [List.reverse_cons, List.append_assoc] using final,
      by simp [original], .cons (decodePage_wire (from_mapError page)) chain⟩

private theorem check_totals {carrier : Carrier} {observed out : Observation} {frames : List Page.Frame}
    (accepted : checkTotals carrier frames observed = .ok out) :
    out = observed ∧ observed.stop.slots = carrier.slots ∧ observed.stop.rows = carrier.rows ∧
      carrier.storedSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.storedChunkBytes frames) ∧
      carrier.rawSize = Int.ofNat (RecursiveSchema.Repeated.Chunk.rawChunkBytes frames) := by
  unfold checkTotals at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i slots
    split at accepted
    · contradiction
    · rename_i rows
      split at accepted
      · contradiction
      · rename_i stored
        split at accepted
        · contradiction
        · rename_i raw
          exact ⟨(Except.ok.inj accepted).symm, Decidable.not_not.mp slots,
            Decidable.not_not.mp rows, Decidable.not_not.mp stored, Decidable.not_not.mp raw⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {binding : Binding schema group}
    {limits : Limits} {out : Observation} (accepted : Parquet.RecursiveSchema.ListPath.Chunk.read limits binding = .ok out) :
    Wire limits (carrierOf binding) out := by
  unfold Parquet.RecursiveSchema.ListPath.Chunk.read at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  rename_i overBytes
  split at accepted
  · contradiction
  rename_i overSlots
  split at accepted
  · contradiction
  rename_i overRows
  let carrier := carrierOf binding
  obtain ⟨frames, parsed, accepted⟩ := bind_ok accepted
  obtain ⟨observed, decoded, accepted⟩ := bind_ok accepted
  obtain ⟨exactOutput, slots, rows, stored, raw⟩ := check_totals accepted
  subst out
  obtain ⟨pages, ordered, eqFrames, chain⟩ := decodeFrames_wire decoded
  have same : observed.pages = pages := by simpa using ordered
  have framesExact : observed.frames = frames := by simpa [Observation.frames, same] using eqFrames
  have parsedExact : Page.readChunk limits.framing carrier.source carrier.span = .ok observed.frames :=
    framesExact ▸ from_mapError parsed
  exact ⟨parsedExact, (Page.readChunk_chain parsedExact).2.2, same ▸ chain, slots, rows,
    framesExact ▸ stored, framesExact ▸ raw, Nat.le_of_not_gt overBytes, Nat.le_of_not_gt overSlots,
    Nat.le_of_not_gt overRows⟩

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : State} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start stop pages) :
    start.slots + (pages.flatMap (·.decoded.atoms)).length = stop.slots ∧
    start.rows + (pages.flatMap (·.decoded.atoms)).countP (·.repetition == 0) = stop.rows := by
  induction wire with
  | nil => simp
  | cons page _ ih =>
    obtain ⟨_, _, _, slots, rows⟩ := page_counts page
    simpa [List.flatMap_cons, List.length_append, List.countP_append, ← Nat.add_assoc, slots, rows] using ih

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
