module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Defs
public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs

/-! One flat LargeBinary field in a canonical modern Arrow V5 IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary.StreamWriter

abbrev Error := Binary.StreamWriter.Error

def serialize (limits : Limits) (field : LargeBinary.Field) (batches : List LargeBinary.Column) :
    Except Error KBytes :=
  Binary.StreamWriter.serializeFor .i64 limits field.name field.nullable batches

def Agrees (field : LargeBinary.Field) (batches : List LargeBinary.Column)
    (decoded : Stream.Observed) : Prop :=
  let observe := Binary.StreamWriter.observe
  decoded.field = field ∧ decoded.batches.map (observe ∘ Binary.Stream.Batch.values) = batches.map observe

instance (field : LargeBinary.Field) (batches : List LargeBinary.Column) (decoded : Stream.Observed) :
    Decidable (Agrees field batches decoded) := by
  unfold Agrees
  infer_instance

/-- Check the generated stream through exact EOS and compare its descriptor
and ordered nullable octets, preserving all batch boundaries. -/
def emit (limits : Limits) (field : LargeBinary.Field) (batches : List LargeBinary.Column) :
    Except Error KBytes := do
  let wire ← serialize limits field batches
  let decoded ← (Stream.read limits .modern wire).mapError .readback
  if Agrees field batches decoded then .ok wire else .error .readbackMismatch

end Silmaril.Formats.Arrow.LargeBinary.StreamWriter
