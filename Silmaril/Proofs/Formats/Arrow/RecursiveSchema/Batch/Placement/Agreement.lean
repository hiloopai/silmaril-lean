module

public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
import Silmaril.Formats.Arrow.RecursiveSchema.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Thms

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement

open Silmaril.Formats.Arrow (Buffer FieldNode)
open Silmaril.Formats.Arrow.RecursiveSchema (Field Schema SchemaWire validArity)
open Silmaril.Formats.Arrow.RecursiveSchema.Batch
open Silmaril.Formats.Arrow.RecursiveSchema.Batch.Placement

private theorem payload_placement {carrier : Carrier} {start : Cursor} {node : FieldNode}
    {validity : Buffer} {kind payload length next}
    (wire : PayloadWire carrier ((start.afterNode node).afterBuffer validity) node kind
      payload length next) :
    indices next = (indices start).afterOwn kind ∧
      PayloadBinding carrier ((indices start).payload kind) payload := by
  cases wire with
  | struct => exact ⟨rfl, trivial⟩
  | values signed region _ =>
    rcases signed with rfl | rfl
    all_goals exact ⟨rfl, region.original⟩
  | offsets region _ _ => exact ⟨rfl, region.original⟩

private theorem batch_agrees {carrier : Carrier} {depth length fields start layouts next}
    (wire : FieldsWire carrier depth length fields start layouts next) :
    ∃ planned, placeFields (placeField depth) fields (indices start) =
      .ok ⟨planned, indices next⟩ ∧ FieldsBinding carrier planned layouts := by
  apply FieldsWire.rec
    (motive_1 := fun depth _ field start layout next _ =>
      ∃ planned, placeField depth field (indices start) =
        .ok (planned, indices next) ∧ FieldBinding carrier planned layout)
    (motive_2 := fun depth _ fields start layouts next _ =>
      ∃ planned, placeFields (placeField depth) fields (indices start) =
        .ok ⟨planned, indices next⟩ ∧ FieldsBinding carrier planned layouts) _ _ _ wire
  · intro depth length name nullable kind children start node validity payload childLength
      childStart childLayouts next arity nodeWire validityWire _ payloadWire _ ih
    obtain ⟨sameStart, original⟩ := payload_placement payloadWire
    obtain ⟨planned, placed, bound⟩ := ih
    refine ⟨.field name nullable kind (indices start) planned, ?_,
      .field nodeWire.original validityWire.original original bound⟩
    simp [placeField, arity, ← sameStart, placed, bind, Except.bind, pure, Except.pure]
  · exact ⟨[], rfl, .nil⟩
  · intro depth length field fields start layout layouts middle next _ _ head tail
    obtain ⟨first, placedFirst, boundFirst⟩ := head
    obtain ⟨rest, placedRest, boundRest⟩ := tail
    exact ⟨first :: rest, by
      simp [placeFields, placedFirst, placedRest, bind, Except.bind, pure, Except.pure],
      .cons boundFirst boundRest⟩

public theorem frame_agrees {limits : Limits} {schema : Schema} {input : KBytes} {offset : Nat}
    (frame : Frame limits schema input offset) :
    ∃ plan, ofSchema limits.schema.depth schema = .ok plan ∧
      plan.next.node = frame.header.nodeCount ∧ plan.next.buffer = frame.header.bufferCount ∧
      FieldsBinding frame.carrier plan.fields frame.layout.fields.layouts := by
  obtain ⟨planned, placed, binding⟩ := batch_agrees frame.layout.fields.wire
  exact ⟨⟨planned, indices frame.layout.fields.next⟩, placed,
    frame.layout.exact_nodes, frame.layout.exact_buffers, binding⟩

private theorem schema_agrees {bytes : KBytes} {depth word count fields used}
    (wire : Silmaril.Formats.Arrow.RecursiveSchema.FieldsWire bytes depth word count fields used) :
    fields.length = count ∧ ∀ start,
      ∃ plan, placeFields (placeField depth) fields start = .ok plan ∧
        plan.next.node = start.node + used ∧ plan.next.buffer ≤ start.buffer + 2 * used ∧
        plan.fields.map FieldPlan.declaration = fields := by
  apply Silmaril.Formats.Arrow.RecursiveSchema.FieldsWire.rec
    (motive_1 := fun depth _ field used _ => ∀ start,
      ∃ planned next, placeField depth field start = .ok (planned, next) ∧
        next.node = start.node + used ∧ next.buffer ≤ start.buffer + 2 * used ∧
        planned.declaration = field)
    (motive_2 := fun depth _ count fields used _ => fields.length = count ∧ ∀ start,
      ∃ plan, placeFields (placeField depth) fields start = .ok plan ∧
        plan.next.node = start.node + used ∧ plan.next.buffer ≤ start.buffer + 2 * used ∧
        plan.fields.map FieldPlan.declaration = fields) _ _ _ wire
  · intro depth position header children used _ arity _ ih start
    obtain ⟨childCount, childPlan⟩ := ih
    obtain ⟨planned, placed, nodeEnd, bufferEnd, declarations⟩ :=
      childPlan (start.afterOwn header.kind)
    refine ⟨.field header.name header.nullable header.kind start planned.fields, planned.next,
      ?_, ?_, ?_, ?_⟩
    · simp [placeField, childCount, arity, placed, bind, Except.bind, pure, Except.pure]
    · simp only [Indices.afterOwn] at nodeEnd
      omega
    · simp only [Indices.afterOwn] at bufferEnd
      split at bufferEnd <;> omega
    · simp [FieldPlan.declaration, declarations]
  · exact ⟨rfl, fun start => ⟨⟨[], start⟩, rfl, by simp⟩⟩
  · intro depth word count position field fields usedHead usedTail _ _ _ head tail
    obtain ⟨counted, tailPlan⟩ := tail
    refine ⟨by simp [counted], ?_⟩
    intro start
    obtain ⟨first, middle, placedFirst, headNode, headBuffers, headDecl⟩ := head start
    obtain ⟨rest, placedRest, tailNode, tailBuffers, tailDecls⟩ := tailPlan middle
    refine ⟨⟨first :: rest.fields, rest.next⟩, ?_, ?_, ?_, ?_⟩
    · simp [placeFields, placedFirst, placedRest, bind, Except.bind, pure, Except.pure]
    · simpa [headNode, Nat.add_assoc] using tailNode
    · change rest.next.buffer ≤ start.buffer + 2 * (usedHead + usedTail)
      omega
    · simp [headDecl, tailDecls]

public theorem readFrame_agrees {limits : Formats.Arrow.RecursiveSchema.Limits} {input : KBytes}
    {schema : Schema} {next : Nat}
    (accepted : Formats.Arrow.RecursiveSchema.readFrame limits input = .ok (schema, next)) :
    ∃ plan, Placement.read limits input = .ok (schema, next, plan) ∧
      plan.next.node ≤ limits.ipc.fields ∧ plan.next.buffer ≤ 2 * plan.next.node ∧
      plan.fields.map FieldPlan.declaration = schema.fields := by
  obtain ⟨_, _, _, _, first, count, used, _, wire, bounded⟩ :=
    Formats.Arrow.RecursiveSchema.readFrame_wire accepted
  obtain ⟨_, placed⟩ := schema_agrees wire
  obtain ⟨plan, built, consumed, buffers, declarations⟩ := placed {}
  exact ⟨plan, by simp [Placement.read, ofSchema, accepted, built, Except.mapError, bind,
    Except.bind, pure, Except.pure], by simpa [consumed] using bounded,
    by simpa [consumed] using buffers, declarations⟩

public theorem placeField_list (depth : Nat) (name : Option String) (nullable : Bool)
    (element : Field) (start : Indices) :
    placeField (depth + 1) (.node name nullable .list [element]) start =
      (placeField depth element ⟨start.node + 1, start.buffer + 2⟩).map
        (fun (child, next) => (.field name nullable .list start [child], next)) := by
  simp only [placeField, validArity, List.length_cons, List.length_nil, beq_self_eq_true,
    Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind, placeFields]
  cases placed : placeField depth element ⟨start.node + 1, start.buffer + 2⟩ <;>
    simp [Indices.afterOwn, payloadRole, placed, pure, Except.pure, Except.map]

public theorem emit_agrees {limits : Formats.Arrow.RecursiveSchema.Limits} {schema : Schema}
    {bytes : KBytes} (emitted : Formats.Arrow.RecursiveSchema.Writer.emit limits schema = .ok bytes) :
    ∃ next plan, Placement.read limits bytes = .ok (schema, next, plan) ∧
      Formats.Arrow.EnvelopeWire limits.ipc bytes.toList next .eos ∧ next + 8 = bytes.len := by
  obtain ⟨next, strict, eos, exactEnd⟩ :=
    (Formats.Arrow.RecursiveSchema.Writer.emit_wire emitted).readback
  have checked := (Formats.Arrow.RecursiveSchema.Stream.read_iff.mp strict).1
  have original : Formats.Arrow.RecursiveSchema.readFrame limits bytes = .ok (schema, next) := by
    unfold Formats.Arrow.RecursiveSchema.Stream.readTrace at checked
    split at checked
    · contradiction
    · rename_i actual offset opened
      split at checked
      have same := Except.ok.inj checked
      have schemaEq : actual = schema :=
        congrArg Formats.Arrow.RecursiveSchema.Stream.Trace.schema same
      have offsetEq : offset = next :=
        congrArg Formats.Arrow.RecursiveSchema.Stream.Trace.schemaEnd same
      rwa [schemaEq, offsetEq] at opened
  obtain ⟨plan, placed, _, _, _⟩ := readFrame_agrees original
  exact ⟨next, plan, placed, eos, exactEnd⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema.Batch.Placement
