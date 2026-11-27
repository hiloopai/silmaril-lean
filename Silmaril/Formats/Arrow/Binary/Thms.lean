module

public import Silmaril.Formats.Arrow.Binary.Defs
import Silmaril.Proofs.Formats.Arrow.Binary.Correctness

public section

namespace Silmaril.Formats.Arrow.Binary

namespace Offsets

theorem readColumn_sound {width : Width} {limits : Limits} {nullable : Bool}
    {node : FieldNode} {buffers : Buffers} {values : Column}
    (read : readColumn width limits nullable node buffers = .ok values) :
    checkColumn limits nullable node buffers = .ok () ∧ ColumnWire width node buffers values :=
  Proofs.Formats.Arrow.Binary.Offsets.readColumn_sound read

theorem slot_octets {width : Width} {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (dataWf : buffers.data.wf = true) (wire : SlotWire width buffers index value) :
    ∃ lo hi valid, OffsetWire width buffers index lo ∧ OffsetWire width buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      value.map KBytes.toList =
        if valid then some ((buffers.data.toList.drop lo).take (hi - lo)) else none :=
  Proofs.Formats.Arrow.Binary.Offsets.slot_octets dataWf wire

end Offsets

theorem readOffset_sound {buffers : Buffers} {index offset : Nat}
    (read : readOffset buffers index = .ok offset) : OffsetWire buffers index offset :=
  Proofs.Formats.Arrow.Binary.Offsets.readOffset_sound read

theorem readSlot_sound {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (read : readSlot buffers index = .ok value) : SlotWire buffers index value :=
  Proofs.Formats.Arrow.Binary.readSlot_sound read

theorem readColumn_sound {limits : Limits} {nullable : Bool} {node : FieldNode}
    {buffers : Buffers} {values : Column}
    (read : readColumn limits nullable node buffers = .ok values) :
    checkColumn limits nullable node buffers = .ok () ∧ ColumnWire node buffers values :=
  Proofs.Formats.Arrow.Binary.readColumn_sound read

theorem bindBody_sound {limits : Limits} {batch : RecordBatch} {body : KBytes}
    {node : FieldNode} {buffers : Buffers}
    (bound : bindBody limits batch body = .ok (node, buffers)) : BodyWire batch body node buffers :=
  Proofs.Formats.Arrow.Binary.bindBody_sound bound

theorem readBatch_sound {limits : Limits} {schemaMetadata recordMetadata body : KBytes}
    {observed : Observed} (read : readBatch limits schemaMetadata recordMetadata body = .ok observed) :
    BatchWire limits schemaMetadata recordMetadata body observed :=
  Proofs.Formats.Arrow.Binary.readBatch_sound read

/-- The observation of a present slot is the exact octet interval, independent
of the shape of its byte rope. The validity bit determines nullness. -/
theorem slot_octets {buffers : Buffers} {index : Nat} {value : Option KBytes}
    (dataWf : buffers.data.wf = true) (wire : SlotWire buffers index value) :
    ∃ lo hi valid, OffsetWire buffers index lo ∧ OffsetWire buffers (index + 1) hi ∧
      lo ≤ hi ∧ Body.validAt buffers.validity index = some valid ∧
      value.map KBytes.toList =
        if valid then some ((buffers.data.toList.drop lo).take (hi - lo)) else none :=
  Proofs.Formats.Arrow.Binary.slot_octets dataWf wire

end Silmaril.Formats.Arrow.Binary
