module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Page
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Chain

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

/-- Each original body is exhausted by the level sections and the signed
word suffix. Returned words occupy exactly the present slots. -/
theorem decodePage_wire {limits : Limits} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodePage limits leaf source frame start remaining rowCeiling = .ok decoded) :
    PageWire limits leaf source frame start remaining rowCeiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.decodePage_wire read

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
    start.state.slot + (Observation.mk pages).levels.length = stop.state.slot ∧
    start.state.rows + (Observation.mk pages).levels.countP LevelSlot.startsRow = stop.state.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.chain_counts wire

/-- Starting with no live list, successful decoding walks consecutive
original pages and attains both independent original footer counts. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    {limits : Limits} {binding : Binding schema group column} {output : Observation}
    (accepted : read limits binding = .ok output) : Wire limits binding output :=
  Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk.read_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
