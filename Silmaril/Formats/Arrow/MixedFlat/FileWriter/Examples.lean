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

#guard match emit {} [⟨"text", false, .primitive .utf8⟩] [] with
  | .error (.schema .unsupportedSchema) => true
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.FileWriter
