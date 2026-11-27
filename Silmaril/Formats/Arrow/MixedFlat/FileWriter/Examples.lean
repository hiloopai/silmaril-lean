module

import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.FileWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.File.Events.Pull.Defs

open Silmaril.Formats.Arrow

namespace Silmaril.Formats.Arrow.MixedFlat.FileWriter

private def empty : OrderedWriter.BatchInput :=
  ⟨0, [.utf8View "t" true [], .int32 "i" false [], .binary "b" true []]⟩

private def one : OrderedWriter.BatchInput :=
  ⟨1, [.utf8View "t" true [some "雪雪雪雪雪"], .int32 "i" false [some (-3)],
    .binary "b" true [some (.leaf 13 255)]]⟩

private def reads (fields : List Field) (inputs : List OrderedWriter.BatchInput) : Bool := Id.run do
  let .ok wire := emit {} fields inputs | return false
  let .ok index := MixedFlat.File.readIndex {} wire | return false
  let .ok observed := readback {} wire index.footer | return false
  let .ok ⟨_, trace⟩ := MixedFlat.File.Events.Pull.readAll {} wire | return false
  return decide (index.footer.fields = fields ∧ index.footer.blocks.length = inputs.length ∧
    observed.map observe = inputs.map (·.observe) ∧
    trace.batches.map (·.rowCount) = inputs.map (·.rowCount) ∧ trace.termination = .eos)

#guard reads empty.fields [one, empty, one]
#guard reads empty.fields []
#guard reads empty.fields [empty]
#guard reads [] [⟨3, []⟩, ⟨0, []⟩]

#guard match emit {} empty.fields [one, ⟨0, []⟩] with
  | .error (.record 1 .schemaMismatch) => true
  | _ => false

#guard match emit { observation := { totalRows := 1 } } empty.fields [one, empty, one] with
  | .error (.ipc (.limit .totalRows)) => true
  | _ => false

private def plain : OrderedWriter.BatchInput :=
  ⟨3, [.utf8 "text" true [none, some "", some "é雪"],
    .utf8View "view" true [some "a", none, some ""],
    .utf8 "other" false [some "", some "雪", some "é"]]⟩

#guard reads plain.fields [plain]
#guard reads plain.fields []

#guard Id.run do
  let .ok wire := emit {} plain.fields [plain] | return false
  let .ok index := MixedFlat.File.readIndex {} wire | return false
  let some block := index.footer.blocks[0]? | return false
  let .ok record := MixedFlat.readMetadata {} 1024 4096 index.footer.fields (MixedFlat.File.metadataSlice wire block)
    | return false
  return decide (index.footer.fields.map (·.kind) = [.primitive .utf8, .view .utf8, .primitive .utf8] ∧
    record.counts = [0] ∧ record.batch.buffers.length = 8)

end Silmaril.Formats.Arrow.MixedFlat.FileWriter
