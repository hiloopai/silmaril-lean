module

public import Silmaril.Formats.Arrow.RecursiveSchema.Defs
import Silmaril.Formats.Arrow.Framing.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.RecursiveSchema

open Silmaril.Formats.Arrow (EnvelopeWire readEnvelope readEnvelope_iff metadata_exact)
open Silmaril.Formats.Arrow.RecursiveSchema

private theorem readFieldsAt_wire {bytes : KBytes} {depth : Nat}
    {readField : Nat → Nat → Except Error (Field × Nat)}
    (fieldLaw : ∀ {position supplied field remaining},
      readField position supplied = .ok (field, remaining) →
      ∃ used, FieldWire bytes depth position field used ∧ remaining + used = supplied)
    {count word supplied fields remaining}
    (accepted : readFieldsAt bytes readField count word supplied = .ok (fields, remaining)) :
    ∃ used, FieldsWire bytes depth word count fields used ∧ remaining + used = supplied := by
  induction count generalizing word supplied fields remaining with
  | zero =>
    simp [readFieldsAt] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨0, .nil, rfl⟩
  | succ count ih =>
    simp only [readFieldsAt, bind, Except.bind] at accepted
    cases offset : Wire.fieldOffset bytes word with
    | error cause => simp [Except.mapError, offset] at accepted
    | ok position =>
      simp only [Except.mapError, offset] at accepted
      cases first : readField position supplied with
      | error cause => simp [first] at accepted
      | ok head =>
        obtain ⟨field, afterHead⟩ := head
        simp only [first] at accepted
        cases rest : readFieldsAt bytes readField count (word + 4) afterHead with
        | error cause => simp [rest] at accepted
        | ok tail =>
          obtain ⟨tailFields, afterTail⟩ := tail
          simp [rest, pure, Except.pure] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          obtain ⟨usedHead, headWire, headBudget⟩ := fieldLaw first
          obtain ⟨usedTail, tailWire, tailBudget⟩ := ih rest
          exact ⟨usedHead + usedTail, .cons offset headWire tailWire, by omega⟩

private theorem readFieldAt_wire {bytes : KBytes} {depth position supplied field remaining}
    (accepted : readFieldAt bytes depth position supplied = .ok (field, remaining)) :
    ∃ used, FieldWire bytes depth position field used ∧ remaining + used = supplied := by
  induction depth generalizing position supplied field remaining with
  | zero => simp [readFieldAt] at accepted
  | succ depth ih =>
    cases supplied with
    | zero => simp [readFieldAt] at accepted
    | succ supplied =>
      simp only [readFieldAt, bind, Except.bind] at accepted
      cases headerRead : Wire.fieldHeader bytes position with
      | error cause => simp [Except.mapError, headerRead] at accepted
      | ok header =>
        simp only [Except.mapError, headerRead] at accepted
        cases arity : validArity header.kind header.childrenCount with
        | false => simp [arity, throw] at accepted
        | true =>
          simp only [arity, Bool.not_true, Bool.false_eq_true, ite_false] at accepted
          cases childrenRead : readFieldsAt bytes (readFieldAt bytes depth)
              header.childrenCount header.childrenFirst supplied with
          | error cause => simp [childrenRead] at accepted
          | ok result =>
            obtain ⟨children, afterChildren⟩ := result
            simp [childrenRead, pure, Except.pure] at accepted
            obtain ⟨rfl, rfl⟩ := accepted
            obtain ⟨used, childrenWire, budget⟩ := readFieldsAt_wire (fun h => ih h) childrenRead
            exact ⟨used + 1, .node headerRead arity childrenWire, by omega⟩

theorem readMessage_wire {limits : Limits} {bytes : KBytes} {schema : Schema}
    (accepted : readMessage limits bytes = .ok schema) :
    SchemaWire limits bytes schema := by
  simp only [readMessage, bind, Except.bind] at accepted
  cases root : Wire.rootFields limits.ipc bytes with
  | error cause => simp [Except.mapError, root] at accepted
  | ok span =>
    obtain ⟨first, count⟩ := span
    simp only [Except.mapError, root] at accepted
    cases fieldsRead : readFieldsAt bytes (readFieldAt bytes limits.depth)
        count first limits.ipc.fields with
    | error cause => simp [fieldsRead] at accepted
    | ok result =>
      obtain ⟨fields, remaining⟩ := result
      simp [fieldsRead, pure, Except.pure] at accepted
      subst schema
      obtain ⟨used, wire, budget⟩ := readFieldsAt_wire readFieldAt_wire fieldsRead
      exact ⟨first, count, used, root, wire, by omega⟩

theorem readFrame_wire {limits : Limits} {input : KBytes} {schema : Schema} {next : Nat}
    (accepted : readFrame limits input = .ok (schema, next)) :
    ∃ size, next = 8 + size ∧
      EnvelopeWire limits.ipc input.toList 0 (.metadata size) ∧
      (input.slice 8 size).toList = (input.toList.drop 8).take size ∧
      SchemaWire limits (input.slice 8 size) schema := by
  unfold readFrame at accepted
  cases wf : input.wf
  · simp [wf, throw, bind, Except.bind] at accepted
  simp only [wf, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind] at accepted
  cases envelope : readEnvelope limits.ipc input 0 with
  | error cause => simp [Except.mapError, envelope] at accepted
  | ok result =>
    cases result with
    | eos => simp [Except.mapError, envelope, throw] at accepted
    | metadata size =>
      simp only [Except.mapError, envelope] at accepted
      cases parsed : readMessage limits (input.slice 8 size) with
      | error cause => simp [parsed] at accepted
      | ok observed =>
        simp [parsed, pure, Except.pure] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨size, rfl, (readEnvelope_iff _ _ _ _ wf).mp envelope,
          metadata_exact wf envelope, readMessage_wire parsed⟩

end Silmaril.Proofs.Formats.Arrow.RecursiveSchema
