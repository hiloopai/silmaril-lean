module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Thms
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Cursor
import Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

public section

theorem step_wire {plan : Plan} {ceiling rep defn : Nat} {start : State} {slot : Slot}
    (accepted : step plan ceiling start rep defn = .ok slot) :
    slot.repetition = rep ∧ slot.definition = defn ∧ StepWire plan ceiling start slot :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.step_wire accepted

/-- The new live depth is determined only by which original wrappers the
current definition reaches. An earlier inner List cannot stay live. -/
theorem StepWire.nextLive {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) :
    (start.consume slot).live =
      if plan.innerEmpty < slot.definition then .inner
      else if plan.outerEmpty < slot.definition then .outer else .closed :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.next_live wire

theorem StepWire.rowStart {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) : slot.startsRow = true ↔ slot.repetition = 0 :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.row_start wire

theorem StepWire.innerStart {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 1) :
    slot.position = .innerStart ∧ start.live ≠ .closed ∧ (start.consume slot).live ≠ .closed :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.inner_start wire rep

theorem StepWire.innerContinue {plan : Plan} {ceiling : Nat} {start : State} {slot : Slot}
    (wire : StepWire plan ceiling start slot) (rep : slot.repetition = 2) :
    slot.position = .innerContinue ∧ start.live = .inner ∧ (start.consume slot).live = .inner :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.inner_continue wire rep

theorem classify_wire {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {out : Classified} (accepted : classify plan ceiling start reps defs = .ok out) :
    SlotsWire plan ceiling start reps defs out.levels out.after :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.classify_wire accepted

theorem SlotsWire.originalLevels {plan : Plan} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List Slot} (wire : SlotsWire plan ceiling start reps defs slots stop) :
    slots.map (·.repetition) = reps ∧ slots.map (·.definition) = defs :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.original_levels wire

/-- A successful page binds the original V1 header, stored body, both
length-prefixed Hybrid sections, and every signed word in order. -/
theorem decodePage_wire {limits : Limits} {plan : Plan} {source : Bytes} {frame : Page.Frame}
    {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    (accepted : decodePage limits plan source frame start remaining ceiling = .ok decoded) :
    PageWire limits plan source frame start remaining ceiling decoded :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.decodePage_wire accepted

theorem ChainWire.counts {limits : Limits} {carrier : Carrier} {start stop : State}
    {frames : List Page.Frame} {pages : List ObservedPage}
    (wire : ChainWire limits carrier start frames pages stop) :
    start.slots + (pages.flatMap (·.decoded.levels)).length = stop.slots ∧
      start.rows + (pages.flatMap (·.decoded.levels)).countP Slot.startsRow = stop.rows :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.chain_counts wire

/-- The checked chunk covers the original bounded interval, carries state
from the closed group start, and meets both original footer counts. -/
theorem read_wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} {limits : Limits}
    {binding : Binding schema group} {out : Observation}
    (accepted : Chunk.read limits binding = .ok out) : Wire limits (carrierOf binding) out :=
  Proofs.Formats.Parquet.RecursiveSchema.TwoList.Chunk.read_wire accepted

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk
