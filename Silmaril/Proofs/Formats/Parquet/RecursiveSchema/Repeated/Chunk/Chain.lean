module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.Footer.PageLessRecursive.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.V2

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Compiled)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

private def WalkResult (limits : Limits) (carrier : Carrier) (cursor : Cursor)
    (budget : Nat) (reversed pages : List ObservedPage) : Prop :=
  ∃ stop tail, pages = reversed.reverse ++ tail ∧ tail.length ≤ budget ∧
    stop.byte = carrier.span.stop ∧ stop.state.slot = carrier.slots ∧
    stop.state.rows = carrier.rows ∧ ChainWire limits carrier cursor stop tail

private theorem walk_final {limits : Limits} {carrier : Carrier} {budget : Nat}
    {cursor : Cursor} {reversed pages : List ObservedPage}
    (ending : cursor.byte = carrier.span.stop)
    (read : walk limits carrier budget cursor reversed = .ok pages) :
    WalkResult limits carrier cursor budget reversed pages := by
  by_cases slots : cursor.state.slot = carrier.slots
  · by_cases rows : cursor.state.rows = carrier.rows
    · have result : reversed.reverse = pages := by
        cases budget <;> simpa [walk, ending, slots, rows] using read
      exact ⟨cursor, [], by simp [result], Nat.zero_le _, ending, slots, rows, .nil cursor⟩
    · cases budget <;> simp [walk, ending, slots, rows] at read
  · cases budget <;> simp [walk, ending, slots] at read

private theorem walk_wire {limits : Limits} {carrier : Carrier} {budget : Nat}
    {cursor : Cursor} {reversed pages : List ObservedPage}
    (read : walk limits carrier budget cursor reversed = .ok pages) :
    WalkResult limits carrier cursor budget reversed pages := by
  induction budget generalizing cursor reversed pages with
  | zero =>
    by_cases ending : cursor.byte = carrier.span.stop
    · exact walk_final ending read
    · simp [walk, ending] at read
  | succ fuel ih =>
    by_cases ending : cursor.byte = carrier.span.stop
    · exact walk_final ending read
    · simp only [walk, ending, ite_false] at read
      cases parsed : Page.readPage limits.framing carrier.bytes carrier.span cursor.byte with
      | error reason => simp [parsed, Except.mapError, bind, Except.bind] at read
      | ok frame =>
        cases decoded : decodeDataPage limits carrier.codec carrier.leaf carrier.bytes frame cursor.state
            (carrier.slots - cursor.state.slot) carrier.rows with
        | error reason => simp [parsed, decoded, Except.mapError, bind, Except.bind] at read
        | ok output =>
          simp only [parsed, decoded, Except.mapError, bind, Except.bind] at read
          let page : ObservedPage := ⟨cursor, frame, output⟩
          obtain ⟨stop, tail, pages, cap, byte, slots, rows, chain⟩ :=
            ih (reversed := page :: reversed) read
          refine ⟨stop, page :: tail, ?_, by simpa using Nat.succ_le_succ cap,
            byte, slots, rows, .more parsed rfl (decodeDataPage_wire decoded) chain⟩
          simpa [List.reverse_cons, List.append_assoc] using pages

public theorem walk_empty_prefix_wire {limits : Limits} {carrier : Carrier}
    {budget : Nat} {cursor : Cursor} {pages : List ObservedPage}
    (read : walk limits carrier budget cursor [] = .ok pages) :
    ∃ stop, pages.length ≤ budget ∧ stop.byte = carrier.span.stop ∧
      stop.state.slot = carrier.slots ∧ stop.state.rows = carrier.rows ∧
      ChainWire limits carrier cursor stop pages := by
  obtain ⟨stop, tail, ordered, cap, byte, slots, rows, chain⟩ := walk_wire read
  simp only [List.reverse_nil, List.nil_append] at ordered
  subst tail
  exact ⟨stop, cap, byte, slots, rows, chain⟩

public theorem chain_frames {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    Page.Chain carrier.span start.byte stop.byte (pages.map ObservedPage.frame) := by
  induction wire with
  | nil cursor => exact .nil cursor.byte
  | more parsed _ _ _ ih => exact .cons (Page.readPage_within parsed).1 ih

public theorem chain_counts {limits : Limits} {carrier : Carrier} {start stop : Cursor}
    {pages : List ObservedPage} (wire : ChainWire limits carrier start stop pages) :
    start.page + pages.length = stop.page ∧
    start.state.slot + (Observation.mk pages).levels.length = stop.state.slot ∧
    start.state.rows + (Observation.mk pages).levels.countP LevelSlot.startsRow = stop.state.rows := by
  induction wire with
  | nil => simp [Observation.levels]
  | @more start stop first rest _ _ bound _ ih =>
    obtain ⟨slots, rows⟩ := dataPage_counts bound
    obtain ⟨pageIndex, slotIndex, rowIndex⟩ := ih
    simp only [Cursor.advance, Observation.levels] at pageIndex slotIndex rowIndex
    simp only [Observation.levels, List.length_cons, List.flatMap_cons, List.length_append, List.countP_append]
    omega

private theorem readFramed_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    {span : Footer.Span}
    (accepted : readFramed limits binding span = .ok output) : FramedWire limits binding span output := by
  unfold readFramed at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · rename_i within
    split at accepted
    · contradiction
    · rename_i bytes
      split at accepted
      · contradiction
      · rename_i slots
        split at accepted
        · contradiction
        · rename_i rows
          split at accepted
          · contradiction
          · cases walked : walk limits (carrierOf binding span) limits.framing.maxPages
                (initial (carrierOf binding span)) [] with
            | error reason => simp [walked, Bind.bind, Except.bind] at accepted
            | ok pages =>
              simp only [walked, Bind.bind, Except.bind] at accepted
              split at accepted
              · contradiction
              rename_i uncompressed
              cases Except.ok.inj accepted
              obtain ⟨stop, cap, byteEnd, slotEnd, rowEnd, chain⟩ := walk_empty_prefix_wire walked
              obtain ⟨_, slotsExact, rowsExact⟩ := chain_counts chain
              have frames := chain_frames chain
              exact ⟨Classical.not_not.mp within, Nat.le_of_not_gt bytes, Nat.le_of_not_gt slots,
                Nat.le_of_not_gt rows, cap, Classical.not_not.mp uncompressed,
                ⟨stop, byteEnd, slotEnd, rowEnd, chain⟩, byteEnd ▸ frames,
                by simpa [initial, carrierOf] using slotsExact.trans slotEnd,
                by simpa [initial, carrierOf] using rowsExact.trans rowEnd⟩

public theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    (accepted : Formats.Parquet.RecursiveSchema.Repeated.Chunk.read limits binding = .ok output) :
    Wire limits binding output := by
  unfold Formats.Parquet.RecursiveSchema.Repeated.Chunk.read at accepted
  cases carrier : binding.storage with
  | framed span encodings original =>
    rw [carrier] at accepted
    have wire := readFramed_wire accepted
    exact ⟨wire.slots, wire.rows, by rw [carrier]; exact wire⟩
  | pageless admitted =>
    simp only [carrier, Except.ok.injEq] at accepted
    subst output
    have empty : Footer.PageLessRecursive.isPageLess binding.rowGroup = true :=
      Snapshot.Checked.admitsPageLessRecursive_isPageLess admitted
    obtain ⟨rows, slots, bytes⟩ := Footer.PageLessRecursive.empty_counts empty
      (List.mem_of_getElem? binding.chunkAt)
    exact ⟨by simp [Observation.levels, slots], by simp [Observation.levels, rows],
      by simp [carrier, Page.columnSpan, Footer.checkDataSpan, bytes]⟩

public theorem noSpan_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    (wire : Wire limits binding output) (empty : binding.span? = none) :
    output.pages = [] ∧ Page.columnSpan snapshot.footer.start binding.chunk.metadata = none := by
  cases storage : binding.storage with
  | framed span encodings original => simp [Binding.span?, storage] at empty
  | pageless admitted => simpa only [storage] using wire.storage

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk
