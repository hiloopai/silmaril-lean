module

public import Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Defs
public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs

/-! Offline comparison of successful incremental schedules on a native IPC carrier. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable

open Silmaril.Relational

/-- Immutable comparison representation for the proof. A live schedule only
needs its ordered input fragments. -/
def reference (wire : KBytes) : KBytes :=
  .leaf wire.len (wire.read 0 wire.len)

structure Completed (limits : Incremental.Limits) (wire : KBytes) where
  fields : List MixedFlat.Field
  batches : List (Delivered fields)
  endOffset : Nat
  ran : ∃ opened last,
    SchemaSteps wire.len (wire.read 0 wire.len) fields (start limits) opened ∧
    RecordSteps wire.len (wire.read 0 wire.len) fields opened batches last ∧
    last.position = wire.len ∧ finish last = .ok endOffset

def Completed.ranges {limits : Incremental.Limits} {wire : KBytes} (run : Completed limits wire) :
    List Stream.BatchRange :=
  run.batches.map (·.record.range)

def Completed.trace {limits : Incremental.Limits} {wire : KBytes} (run : Completed limits wire) :
    Stream.Events.EventStream :=
  .ok ⟨MixedFlat.Events.schema run.fields, ⟨run.batches.map Delivered.event, .eos⟩⟩

abbrev Projection :=
  (signature : Scan.Schema MixedFlat.Field Unit) → Scan.Projection signature

def Completed.project {limits : Incremental.Limits} {wire : KBytes}
    (run : Completed limits wire) (projection : Projection) : Stream.Events.EventStream :=
  run.trace.scan projection (fun _ _ => some true)

/-- Independently check the writer's ordered observation on the immutable
packed reference. Per-stream incremental budgets are carried by Completed. -/
def checkWriterReadback (limits : MixedFlat.Limits) (wire : KBytes)
    (fields : List MixedFlat.Field) (batches : List OrderedWriter.BatchInput) : Bool :=
  match Stream.read limits (reference wire) with
  | .error _ => false
  | .ok decoded =>
    decide (decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map OrderedWriter.BatchInput.observe)

end Silmaril.Formats.Arrow.MixedFlat.Stream.Incremental.Portable
