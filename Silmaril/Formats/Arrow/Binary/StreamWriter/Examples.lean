module

public import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.Binary.StreamWriter.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.Binary.StreamWriter.Examples

def nullableField : Binary.Field := ⟨"payload", true⟩

def requiredField : Binary.Field := ⟨"raw_雪", false⟩

def nullableBatches : List Binary.Column :=
  [[none, some .empty, some (.leaf 1 0xff ++ .leaf 2 0x8000), none, some (.leaf 3 0x7a0078),
    some .empty, none, some (.leaf 1 42), some (.leaf 1 0xfe), none],
   [], [none, none], [some .empty]]

def requiredBatch : Binary.Column := [some .empty, some (.leaf 3 0x81ff00)]

def cases : List (String × Binary.Field × List Binary.Column) :=
  [("nullable", nullableField, nullableBatches),
   ("required", requiredField, [requiredBatch]),
   ("schema_only", requiredField, []),
   ("empty_batch", requiredField, [[]])]

private def checks (field : Binary.Field) (batches : List Binary.Column) : Bool :=
  match emit {} field batches with
  | .error _ => false
  | .ok wire =>
    match Stream.read {} .modern wire with
    | .error _ => false
    | .ok decoded =>
      decide (Agrees field batches decoded) &&
        decoded.eosOffset + 8 == wire.len &&
        (wire.slice decoded.eosOffset 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]

#guard cases.all fun (_, field, batches) => checks field batches

private def fails (result : Except Error KBytes) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard fails (emit {} requiredField [[], [none]]) (.record 1 .nullInRequired)
#guard fails (emit {} nullableField [[some (KBytes.zeros (2^31))]])
  (.record 0 (.signedOffsetExtent (2^31)))
#guard fails (emit {} nullableField [[some (.node 1 .empty .empty)]])
  (.record 0 (.ipc (.malformed .source)))
#guard fails (emit { bodyBytes := 7 } nullableField [[]]) (.record 0 (.ipc (.limit .bodyBytes)))
#guard match emit { bodyBytes := 8 } nullableField [[]] with
  | .ok _ => true
  | .error _ => false

#guard fails (emit { rows := 0 } nullableField [[], [none]]) (.record 1 (.ipc (.limit .rows)))
#guard fails (emit { batches := 0 } nullableField [[]]) (.ipc (.limit .batches))
#guard fails (emit { fields := 0 } nullableField []) (.ipc (.limit .fields))
#guard fails (emit { metadataBytes := 1 } nullableField []) (.ipc (.limit .metadataBytes))
#guard fails (emit { metadataBytes := Wire.schemaSize nullableField } nullableField [[]])
  (.record 0 (.ipc (.limit .metadataBytes)))

end Silmaril.Formats.Arrow.Binary.StreamWriter.Examples
