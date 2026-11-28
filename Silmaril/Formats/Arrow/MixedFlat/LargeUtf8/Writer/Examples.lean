module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Defs


namespace Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Examples

private def batch (rows : Nat) (text : List (Option String)) (numbers : List (Option Int32))
    (binary : List (Option KBytes)) (required : List (Option String)) (plain : List (Option String)) :
    BatchInput :=
  ⟨rows, [.largeUtf8 "text" true text, .existing (.int32 "number" false numbers),
    .existing (.binary "view" true binary), .largeUtf8 "wide_雪" false required,
    .existing (.utf8 "plain" true plain)]⟩

private def bytes (value : String) : KBytes := Arrow.LargeUtf8.StreamWriter.encodeValue value

private def first : BatchInput :=
  batch 4 [none, some "", some "雪🙂", some "é"] [some (-7), some 0, some 12, some 2147483647]
    [some (bytes "0123456789abcdef"), none, some .empty, some (.leaf 2 0xff00)]
    [some "", some ("a".push (Char.ofNat 0) ++ "b"), some "ééééé", some "𐍈"]
    [some "", none, some "a", some "雪"]

private def empty : BatchInput := batch 0 [] [] [] [] []

private def last : BatchInput :=
  batch 2 [some "", none] [some (-2147483648), some 7] [some .empty, none]
    [some "雪", some ""] [some "plain", some ""]

private def backwards (batch : BatchInput) : BatchInput := ⟨batch.rowCount, batch.columns.reverse⟩

public def cases : List (String × List Field × List BatchInput) :=
  [("mixed", empty.fields, [first, empty, last]),
   ("reversed", (backwards empty).fields, ([first, empty, last].map backwards)),
   ("schema_only", empty.fields, []),
   ("empty_batch", empty.fields, [empty]),
   ("zero_width", [], [⟨3, []⟩, ⟨0, []⟩, ⟨2, []⟩])]

private def checks (fields : List Field) (batches : List BatchInput) : Bool :=
  match emit {} fields batches with
  | .error _ => false
  | .ok wire =>
    match Stream.read {} .modern wire with
    | .error _ => false
    | .ok decoded =>
      match decoded.trace.termination with
      | .error .. => false
      | .eos offset =>
        decide (Agrees fields batches decoded) && offset + 8 == wire.len &&
          (wire.slice offset 8).toList == [255, 255, 255, 255, 0, 0, 0, 0]

#guard cases.all fun (_, fields, batches) => checks fields batches

private def checksRecord (input : BatchInput) (counts : List Nat) (widths : List Nat) : Bool :=
  match emitRecord {} input with
  | .error _ => false
  | .ok record =>
    record.output.metadata.batch.rowCount == input.rowCount &&
      record.output.metadata.counts == counts &&
      record.physical.map (·.parts.length) == widths &&
      match LargeUtf8.readBatch {} (Wire.schema input.fields) record.output.metadataBytes record.output.body with
      | .error _ => false
      | .ok decoded => decide (observeBatch decoded = input.observe)

#guard checksRecord first [1] [3, 2, 3, 3, 3]
#guard checksRecord (backwards first) [1] [3, 3, 3, 2, 3]
#guard checksRecord empty [0] [3, 2, 2, 3, 3]
#guard checksRecord ⟨3, []⟩ [] []

private def rejects (result : Except Error KBytes) (expected : Error) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => decide (actual = expected)

private def rejectsBatch (limits : MixedFlat.Limits) (input : BatchInput) (cause : RecordError) : Bool :=
  rejects (emit limits input.fields [input]) (.record 0 cause)

#guard rejectsBatch {} ⟨1, [.largeUtf8 "u" false [none]]⟩ (.largeUtf8 0 .nullInRequired)
#guard rejectsBatch {} ⟨1, [.existing (.int32 "i" true [none]), .largeUtf8 "u" true []]⟩
  (.ordered (.field 1 (.rowCount 1 1 0)))
#guard rejectsBatch { totalDataBuffers := 0 } first (.ordered (.metadata .totalDataBufferLimit))
#guard rejects (emit {} empty.fields [empty, backwards last]) (.record 1 (.ordered .schemaMismatch))
#guard rejects (emit { observation := { ipc := { batches := 0 } } } empty.fields [empty])
  (.ipc (.limit .batches))
#guard rejects (emit { observation := { totalRows := 3 } } [] [⟨3, []⟩, ⟨1, []⟩])
  (.ipc (.limit .totalRows))
#guard rejects (emit { observation := { totalCells := 29 } } empty.fields [first, empty, last])
  (.ipc (.limit .totalCells))
#guard rejects (emit { observation := { ipc := { fields := 4 } } } empty.fields [])
  (.ipc (.limit .fields))
#guard rejects (emit { observation := { ipc := { metadataBytes := 1 } } } empty.fields [])
  (.ipc (.limit .metadataBytes))

-- One bitmap byte, two i64 offsets and ten UTF-8 bytes pad to 40 bytes.
private def multibyte : BatchInput := ⟨1, [.largeUtf8 "u" true [some "ééééé"]]⟩

#guard rejectsBatch { observation := { ipc := { bodyBytes := 39 } } } multibyte
  (.largeUtf8 0 (.ipc (.limit .bodyBytes)))
#guard match emit { observation := { ipc := { bodyBytes := 40 } } } multibyte.fields [multibyte] with
  | .ok _ => true
  | .error _ => false

-- Plain Utf8 through the established ordered writer still requires its
-- explicit profile. The mixed reader's default admission still rejects 20.
#guard match OrderedWriter.emit {} [⟨"plain", true, .primitive .utf8⟩] [] with
  | .error .unsupportedSchema => true
  | _ => false

#guard match MixedFlat.readSchema {} (Wire.schema empty.fields) with
  | .error (.unsupported (.fieldType 20)) => true
  | _ => false

end Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Examples
