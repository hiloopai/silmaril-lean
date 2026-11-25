module

import Silmaril.Parse.ByteParse.Thms
import Silmaril.Parse.DecodeGraph.ByteParse.Thms
import Silmaril.Parse.DecodeGraph.KBytes.Thms

namespace Silmaril.Parse.DecodeGraph.Examples

private def rope : KBytes := .node 3 (.leaf 1 0x90) (.leaf 2 0xCCC3)

theorem kbyte_nonzero_cursor : kbyte rope 2 1 = .ok 0xC3 2 := rfl

theorem kbyte_bounded_eof : kbyte rope 2 2 = .err ⟨2, .eof⟩ := rfl

theorem byteArray_same_cursor : ByteParse.byte rope.toByteArray 2 1 = .ok 0xC3 2 :=
  (kbyte_eq_byte rope rfl 2 1).symm.trans kbyte_nonzero_cursor

theorem kbyte_exact_at_window {input : Input Unit KBytes} {value endPos}
    (valid : ValidWindow .kbytes input) :
    (input, (value, endPos)) ∈ successes (fun (_ : Unit) => kbyte) ↔
      (input, (value, endPos)) ∈ overView .kbytes (ofGrammar fun _ => ByteParse.Spec.byte) := by
  obtain ⟨wf, start, bound⟩ := valid
  let arrayInput : Input Unit ByteArray := ⟨(), input.bytes.toByteArray, input.stop, input.pos⟩
  have validArray : ValidWindow .byteArray arrayInput := ⟨trivial, start, bound⟩
  have run : kbyte input.bytes input.stop input.pos = ByteParse.byte input.bytes.toByteArray input.stop input.pos :=
    kbyte_eq_byte _ wf _ _
  constructor
  · intro success
    have arraySuccess : (arrayInput, (value, endPos)) ∈ ofParser ByteParse.byte := run.symm.trans success
    exact ⟨wf, (soundFor_ofParser.mpr ByteParse.sound_byte validArray arraySuccess).2⟩
  · rintro ⟨_, spec⟩
    have arraySuccess := completeFor_ofParser.mpr ByteParse.complete_byte
      (input := arrayInput) (result := (value, endPos)) validArray ⟨trivial, spec⟩
    exact run.trans arraySuccess

end Silmaril.Parse.DecodeGraph.Examples
