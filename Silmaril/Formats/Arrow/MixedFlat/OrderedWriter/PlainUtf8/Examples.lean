module

import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs

namespace Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.PlainUtf8

private def mixed : BatchInput :=
  ⟨3, [.utf8 "p" true [none, some "", some "é雪"],
    .int32 "i" false [some (-7), some 0, some 9],
    .utf8View "v" true [some "é", none, some ""],
    .utf8 "q" false [some "", some "é", some "雪"]]⟩

#guard Id.run do
  let profile := fun fields => fields == mixed.fields
  let .ok header := emitSchemaWith {} mixed.fields profile | return false
  let .ok (.metadata size) := readEnvelope {} header 0 | return false
  let .ok fields := MixedFlat.readSchema {} (header.slice 8 size) | return false
  let .ok record := emitRecordWith {} mixed profile | return false
  let .ok decoded := MixedFlat.readParsed {} fields record.output.metadata record.output.body | return false
  return decide (fields.map (·.kind) = [.primitive .utf8, .primitive .int32, .view .utf8, .primitive .utf8] ∧
    fields = mixed.fields ∧ record.output.metadata.counts = [0] ∧
    record.plan.assignment.groups.map (·.buffers.length) = [3, 2, 2, 3] ∧
    (decoded.rowCount, Writer.observeColumns decoded.columns) = mixed.observe)

#guard match emitSchema {} mixed.fields with
  | .error .unsupportedSchema => true
  | _ => false
#guard match emitRecord {} mixed with
  | .error .unsupportedSchema => true
  | _ => false

#guard match (Column.utf8 "p" false [none]).compile {} 1 2 with
  | .error (.field 2 (.nullInRequired 2)) => true
  | _ => false
#guard match (Column.utf8 "p" true [some "é雪"]).compile { observation := { ipc := { bodyBytes := 4 } } } 1 2 with
  | .error (.ipc (.limit .bodyBytes)) => true
  | _ => false
#guard match (Column.utf8 "p" true [some "é雪"]).compile { view := { valueBytes := 0 } } 1 2 with
  | .ok physical => physical.count.isNone
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.PlainUtf8
