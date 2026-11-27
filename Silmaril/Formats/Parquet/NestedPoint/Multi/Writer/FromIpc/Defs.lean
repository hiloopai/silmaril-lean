module

public import Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.Defs

/-! Consume checked signed STRUCT IPC through EOS, then write the NestedPoint profile. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc

open Arrow.StructInt32.Stream (Observed)
open NestedPoint (Row)

structure Limits where
  ipc : Arrow.ObservationLimits := {}
  parquet : Writer.Limits := {}

inductive Error where
  | source (cause : Arrow.StructInt32.Stream.Error)
  | requiredness (column : Nat) (actualNullable : Bool)
  | requiredNull (group row : Nat)
  | writer (cause : Writer.Error)
  deriving DecidableEq, Repr

def bindRow (group row : Nat) : ToIpc.NativeRow → Except Error Row
  | none => .ok none
  | some (some signed, wide) => .ok (some (signed, wide))
  | some (none, _) => .error (.requiredNull group row)

def bindGroup (group : Nat) (rows : List ToIpc.NativeRow) : Except Error (List Row) :=
  rows.zipIdx.mapM fun (row, index) => bindRow group index row

def bindInput (observed : Observed Int64) : Except Error Writer.Input := do
  let field := observed.field
  if field.left.nullable then return ← throw (.requiredness 0 true)
  if !field.right.nullable then return ← throw (.requiredness 1 false)
  let groups ← observed.batches.zipIdx.mapM fun (batch, group) => bindGroup group batch.rows
  return ⟨field.name, field.left.name, field.right.name, groups⟩

/-- Original native source errors, including late framing failures, precede
every writer decision. -/
def convert (limits : Limits) (wire : KBytes) : Except Error Encoded := do
  let observed ← (Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire).mapError .source
  let input ← bindInput observed
  (emit limits.parquet input).mapError .writer

structure Readback (limits : Limits) (wire : KBytes) (output : Encoded) : Prop where
  data : ∃ (observed : Observed Int64) (input : Writer.Input) (size : Nat),
    Arrow.StructInt32.Stream.readFor .int64 limits.ipc wire = .ok observed ∧
    wire.wf = true ∧ Arrow.readEnvelope limits.ipc.ipc wire 0 = .ok (.metadata size) ∧
    Arrow.StructInt32.readSchemaFor .int64 limits.ipc.ipc (wire.slice 8 size) = .ok observed.field ∧
    Arrow.StructInt32.Stream.BatchesWireFor .int64 limits.ipc observed.field wire
      limits.ipc.ipc.batches 0 (8 + size) observed.batches ∧
    input.field = observed.field ∧ input.groups.map (List.map ToIpc.nativeRow) = observed.batches.map (·.rows) ∧
    Writer.Readback limits.parquet input output

end Silmaril.Formats.Parquet.NestedPoint.Multi.Writer.FromIpc
