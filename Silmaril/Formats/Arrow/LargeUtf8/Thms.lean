module

public import Silmaril.Formats.Arrow.LargeUtf8.Defs
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.Correctness

public section

namespace Silmaril.Formats.Arrow.LargeUtf8

theorem readColumn_sound {limits : Limits} {nullable : Bool} {node : FieldNode}
    {buffers : Buffers} {values : Column}
    (read : readColumn limits nullable node buffers = .ok values) :
    Binary.checkColumn limits nullable node buffers = .ok () ∧ ColumnWire node buffers values :=
  Proofs.Formats.Arrow.LargeUtf8.readColumn_sound read

/-- Both i64 offsets refer to the original data descriptor. Present values
certify valid UTF-8 and re-encode to exactly the selected octets. -/
theorem slot_octets {buffers : Buffers} {index : Nat} {value : Option String}
    (wf : buffers.data.wf = true) (wire : SlotWire buffers index value) :
    ∃ lo hi valid, LargeBinary.OffsetWire buffers index lo ∧ LargeBinary.OffsetWire buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      if valid then (buffers.data.slice lo (hi - lo)).toByteArray.IsValidUTF8 ∧
        value.map (fun text => text.toByteArray.data.toList) =
          some ((buffers.data.toList.drop lo).take (hi - lo))
      else value = none :=
  Proofs.Formats.Arrow.LargeUtf8.slot_octets wf wire

end Silmaril.Formats.Arrow.LargeUtf8
