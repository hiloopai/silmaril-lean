module

public import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs
meta import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Examples

def nullableField : LargeUtf8.Field := ⟨"text", true⟩

def requiredField : LargeUtf8.Field := ⟨"text_雪", false⟩

def cases : List (String × LargeUtf8.Field × List LargeUtf8.Column) :=
  [("nullable", nullableField,
    [[none, some "", some "é雪🙂", none, some "x\x00z", some "", none, some "a", some "𐍈", none],
     [], [none, none], [some ""]]),
   ("required", requiredField, [[some "", some "ééééé"]]),
   ("schema_only", requiredField, []),
   ("empty_batch", requiredField, [[]])]

private def checks (field : LargeUtf8.Field) (batches : List LargeUtf8.Column) : Bool :=
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

#guard fails (emit {} requiredField [[], [none]]) (.serialize (.record 1 .nullInRequired))
#guard fails (emit { rows := 0 } nullableField [[], [none]])
  (.serialize (.record 1 (.ipc (.limit .rows))))
#guard fails (emit { batches := 0 } nullableField [[]]) (.serialize (.ipc (.limit .batches)))
#guard fails (emit { fields := 0 } nullableField []) (.serialize (.ipc (.limit .fields)))
#guard fails (emit { metadataBytes := 1 } nullableField []) (.serialize (.ipc (.limit .metadataBytes)))
#guard fails (emit { metadataBytes := 167 } nullableField [[]])
  (.serialize (.record 0 (.ipc (.limit .metadataBytes))))
#guard match emit { metadataBytes := 168 } nullableField [[]] with
  | .ok _ => true
  | .error _ => false

-- One bitmap byte, two i64 words, and ten UTF-8 bytes pad to 40 bytes.
#guard fails (emit { bodyBytes := 39 } nullableField [[], [some "ééééé"]])
  (.serialize (.record 1 (.ipc (.limit .bodyBytes))))
#guard match emit { bodyBytes := 40 } nullableField [[], [some "ééééé"]] with
  | .ok _ => true
  | .error _ => false

end Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Examples
