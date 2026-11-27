module

public import Silmaril.Formats.Parquet.ListFile.Writer.Defs
public import Silmaril.Formats.Arrow.ListInt32.Stream.Defs

/-! One checked native Arrow LIST stream to the canonical Parquet LIST writer. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ListFile.Writer.FromIpc

structure Limits where
  ipc : Arrow.ListInt32.Stream.Limits := {}
  parquet : Writer.Limits := {}

inductive Error where
  | source (cause : Arrow.ListInt32.Stream.Error)
  | childName (actual : String)
  | writer (cause : Writer.Error)
  deriving DecidableEq, Repr

def writerInput (observed : Arrow.ListInt32.Stream.Observed) : Writer.Input :=
  ⟨observed.field.name, observed.field.childName, observed.batches.map (·.rows)⟩

/-- The comparison retains names, nullable nested rows and batch boundaries.
Physical ranges and children hidden by null parents carry no observed value. -/
def observation (observed : Arrow.ListInt32.Stream.Observed) :
    Arrow.ListInt32.Field × List (List ListPage.Row) :=
  (observed.field, observed.batches.map (·.rows))

/-- Finish the original source, including EOS, before considering any writer
admission. An original batch error keeps its index and exact cause. -/
def convert (limits : Limits) (input : KBytes) : Except Error Writer.Encoded := do
  let observed ← (Arrow.ListInt32.Stream.read limits.ipc input).mapError .source
  if observed.field.childName ≠ "element" then return ← throw (.childName observed.field.childName)
  (Writer.emit limits.parquet (writerInput observed)).mapError .writer

structure Readback (limits : Limits) (input : KBytes) (output : Writer.Encoded) : Prop where
  data : ∃ observed checked size,
    Arrow.ListInt32.Stream.read limits.ipc input = .ok observed ∧
    observed.field.childName = "element" ∧ input.wf = true ∧
    Arrow.readEnvelope limits.ipc.ipc input 0 = .ok (.metadata size) ∧
    Arrow.ListInt32.readSchema limits.ipc.ipc (input.slice 8 size) = .ok observed.field ∧
    Arrow.ListInt32.Stream.BatchesWire limits.ipc input limits.ipc.ipc.batches 0 0 (8 + size) observed.batches ∧
    Writer.emit limits.parquet (writerInput observed) = .ok output ∧
    output.Layout limits.parquet (writerInput observed) ∧
    ListFile.openFile limits.parquet.readback.file output.bytes = .ok checked ∧
    ListFile.OpenWire limits.parquet.readback.file output.bytes checked ∧
    checked.shape.outer.name = observed.field.name ∧ checked.shape.element.name = observed.field.childName ∧
    checked.snapshot.groupCount = observed.batches.length ∧
    Writer.readGroups limits.parquet.readback checked = .ok (observed.batches.map (·.rows)) ∧
    List.Forall₂ (Multi.GroupWire limits.parquet.readback.maxGroupSlots checked)
      (List.range checked.snapshot.groupCount) (observed.batches.map (·.rows))

end Silmaril.Formats.Parquet.ListFile.Writer.FromIpc
