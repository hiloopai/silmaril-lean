module

public import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Examples

def nullableField : LargeBinary.Field := ⟨"payload", true⟩

def requiredField : LargeBinary.Field := ⟨"raw_雪", false⟩

def nullableBatches : List LargeBinary.Column :=
  [[none, some .empty, some (.leaf 1 0xff ++ .leaf 2 0x8000), none, some (.leaf 3 0x7a0078),
    some .empty, none, some (.leaf 1 42), some (.leaf 1 0xfe), none],
   [], [none, none], [some .empty]]

def requiredBatch : LargeBinary.Column := [some .empty, some (.leaf 3 0x81ff00)]

def cases : List (String × LargeBinary.Field × List LargeBinary.Column) :=
  [("nullable", nullableField, nullableBatches),
   ("required", requiredField, [requiredBatch]),
   ("schema_only", requiredField, []),
   ("empty_batch", requiredField, [[]])]

private def checks (field : LargeBinary.Field) (batches : List LargeBinary.Column) : Bool :=
  match emit {} field batches with
  | .error _ => false
  | .ok wire =>
    match Stream.read {} .modern wire with
    | .error _ => false
    | .ok decoded =>
      decide (Agrees field batches decoded) && decoded.eosOffset + 8 == wire.len &&
        (wire.slice decoded.eosOffset 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]

#guard cases.all fun (_, field, batches) => checks field batches

private def fails (result : Except Error KBytes) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard fails (emit {} requiredField [[], [none]]) (.record 1 .nullInRequired)
#guard fails (emit {} nullableField [[some (KBytes.zeros (2^63))]])
  (.record 0 (.signedOffsetExtent (2^63)))
#guard fails (emit {} nullableField [[some (.node 1 .empty .empty)]])
  (.record 0 (.ipc (.malformed .source)))
#guard fails (emit { rows := 0 } nullableField [[], [none]]) (.record 1 (.ipc (.limit .rows)))
#guard fails (emit { batches := 0 } nullableField [[]]) (.ipc (.limit .batches))
#guard fails (emit { fields := 0 } nullableField []) (.ipc (.limit .fields))
#guard fails (emit { metadataBytes := 1 } nullableField []) (.ipc (.limit .metadataBytes))
#guard fails (emit { metadataBytes := Binary.StreamWriter.Wire.schemaSizeFor nullableField.name }
    nullableField [[]]) (.record 0 (.ipc (.limit .metadataBytes)))

private def short : LargeBinary.Column := [none, some .empty, some (.leaf 3 0x8000ff)]

#guard fails (emit { bodyBytes := 47 } nullableField [short]) (.record 0 (.ipc (.limit .bodyBytes)))
#guard match emit { bodyBytes := 48 } nullableField [short] with
  | .ok _ => true
  | .error _ => false

-- Preflight only. A compact zero leaf isolates the difference in signed
-- offset width without emitting a multi-gigabyte record.
#guard match Binary.StreamWriter.checkRecordFor .i64 { bodyBytes := 2^32 } true
    [some (KBytes.zeros (2^31))], Binary.StreamWriter.checkRecord { bodyBytes := 2^32 } true
    [some (KBytes.zeros (2^31))] with
  | .ok node, .error (.signedOffsetExtent bytes) => node.length = 1 ∧ bytes = 2^31
  | _, _ => false

end Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Examples
