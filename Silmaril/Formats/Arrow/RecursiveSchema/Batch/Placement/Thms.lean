module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
import Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement.Agreement

namespace Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement

@[expose] public section

/-- The List's validity is at the current buffer position. Its offset
descriptor comes next and its only child starts after both descriptors. -/
theorem placeField_list (depth : Nat) (name : Option String) (nullable : Bool)
    (element : Field) (start : Indices) :
    placeField (depth + 1) (.node name nullable .list [element]) start =
      (placeField depth element ⟨start.node + 1, start.buffer + 2⟩).map
        (fun (child, next) => (.field name nullable .list start [child], next)) :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement.placeField_list depth name nullable element start

theorem list_offsets (start : Indices) :
    start.payload .list = some (start.buffer + 1, .offsets32) := rfl

/-- Native schema errors are reported before constructing a placement. -/
theorem read_schema_error {limits : RecursiveSchema.Limits} {input : KBytes}
    {cause : RecursiveSchema.Error}
    (original : RecursiveSchema.readFrame limits input = .error cause) :
    read limits input = .error (.schema cause) := by
  simp [read, original, Except.mapError, bind, Except.bind]

/-- The accepted native schema always has a plan within the original field
budget. Erasing the ordinals gives the exact original declaration tree. -/
theorem readFrame_agrees {limits : RecursiveSchema.Limits} {input : KBytes}
    {schema : Schema} {next : Nat}
    (accepted : RecursiveSchema.readFrame limits input = .ok (schema, next)) :
    ∃ plan, read limits input = .ok (schema, next, plan) ∧
      plan.next.node ≤ limits.ipc.fields ∧ plan.next.buffer ≤ 2 * plan.next.node ∧
      plan.fields.map FieldPlan.declaration = schema.fields :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement.readFrame_agrees accepted

/-- Each schema-only ordinal names the original descriptor consumed by
the checked batch reader. Both descriptor vectors are exhausted exactly. -/
theorem frame_agrees {limits : Batch.Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) :
    ∃ plan, ofSchema limits.schema.depth schema = .ok plan ∧
      plan.next.node = frame.header.nodeCount ∧ plan.next.buffer = frame.header.bufferCount ∧
      FieldsBinding frame.carrier plan.fields frame.layout.fields.layouts :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement.frame_agrees frame

/-- The existing native schema writer yields the same planned declaration
followed immediately by the exact modern EOS. -/
theorem emit_agrees {limits : RecursiveSchema.Limits} {schema : Schema} {bytes : KBytes}
    (emitted : RecursiveSchema.Writer.emit limits schema = .ok bytes) :
    ∃ next plan, read limits bytes = .ok (schema, next, plan) ∧
      EnvelopeWire limits.ipc bytes.toList next .eos ∧ next + 8 = bytes.len :=
  Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement.emit_agrees emitted

end

end Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement
