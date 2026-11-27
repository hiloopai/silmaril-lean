module

public import Silmaril.Formats.Arrow.LargeBinary.Defs
import Silmaril.Formats.Arrow.Binary.Thms

public section

namespace Silmaril.Formats.Arrow.LargeBinary

theorem readColumn_sound {limits : Limits} {nullable : Bool} {node : FieldNode}
    {buffers : Buffers} {values : Column}
    (read : readColumn limits nullable node buffers = .ok values) :
    Binary.checkColumn limits nullable node buffers = .ok () ∧ ColumnWire node buffers values :=
  Binary.Offsets.readColumn_sound read

theorem slot_octets {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (dataWf : buffers.data.wf = true) (wire : SlotWire buffers index value) :
    ∃ lo hi valid, OffsetWire buffers index lo ∧ OffsetWire buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      value.map KBytes.toList =
        if valid then some ((buffers.data.toList.drop lo).take (hi - lo)) else none :=
  Binary.Offsets.slot_octets dataWf wire

end Silmaril.Formats.Arrow.LargeBinary
