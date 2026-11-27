module

import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs

namespace Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.PlainUtf8

private def text : BatchInput :=
  ⟨3, [.utf8 "t" true [none, some "", some "雪é"], .utf8View "v" false [some "", some "a", some "é"]]⟩

private def empty : BatchInput := ⟨0, [.utf8 "t" true [], .utf8View "v" false []]⟩

private def accepts (inputs : List BatchInput) : Bool := Id.run do
  let .ok wire := emitWith {} text.fields inputs (fun fields => fields == text.fields) | return false
  let .ok observed := Stream.read {} wire | return false
  let .ok ⟨signature, trace⟩ := Stream.Events.readAll {} wire | return false
  let eos := wire.len - 8
  let .ok .eos := readEnvelope {} wire eos | return false
  return decide (observed.fields = text.fields ∧
    observed.batches.map StreamWriter.observeBatch = inputs.map BatchInput.observe ∧
    List.ofFn (fun i : Fin signature.width => (signature.kind i).1) = text.fields ∧
    trace.batches.map (·.rowCount) = inputs.map (·.rowCount) ∧ trace.termination = .eos)

#guard accepts [text, empty, text]
#guard accepts []
#guard accepts [empty]

#guard match emit {} text.fields [text] (fun _ => true) with
  | .error .unsupportedSchema => true
  | _ => false
#guard match serialize {} text.fields [] (fun _ => true) with
  | .error .unsupportedSchema => true
  | _ => false
#guard match emitWith {} text.fields [] (fun _ => false) with
  | .error .unsupportedSchema => true
  | _ => false

#guard
  let different : BatchInput := ⟨0, [.utf8View "t" true [], .utf8View "v" false []]⟩
  match emitWith {} text.fields [text, different] (fun _ => true) with
  | .error (.record 1 .schemaMismatch) => true
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.PlainUtf8
