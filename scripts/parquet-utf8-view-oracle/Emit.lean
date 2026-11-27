module

import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs
meta import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet
open Parquet.Plain.ByteArray
open Arrow.MixedFlat

private def load (directory : System.FilePath) (file : String) : IO Bytes := do
  return ⟨← IO.FS.readBinFile (directory / (file ++ ".parquet"))⟩

private def emit (directory : System.FilePath) (file : String) (layout : FlatColumn.Layout)
    (annotation : Utf8.Annotation) (expected : List Nat) : IO Unit := do
  let bytes ← load directory file
  let .ok checked := Utf8.openFile {} bytes "label" layout |
    throw (IO.userError s!"annotation not admitted in {file}")
  unless checked.annotation == annotation && checked.physical.binding.columnOrdinal == 1 do
    throw (IO.userError "wrong original selected leaf or spelling")
  let .ok wire := Utf8.convert {} {} bytes "label" layout |
    throw (IO.userError s!"checked conversion failed for {file}")
  let .ok decoded := Stream.read {} wire | throw (IO.userError "Utf8View readback failed")
  unless decoded.fields == [⟨"label", layout == .optional, .view .utf8⟩] &&
      decoded.batches.map (·.observed.rowCount) == expected do
    throw (IO.userError "wrong text field or ordered group boundaries")
  IO.FS.writeBinFile (directory / (file ++ ".arrows")) wire.toByteArray

public def main (args : List String) : IO Unit := do
  let [path, laterHeader] := args | throw (IO.userError "expected fixture directory and header offset")
  let some header := laterHeader.toNat? | throw (IO.userError "invalid later frame offset")
  let directory := System.FilePath.mk path
  emit directory "v1" .optional .logicalAndConverted [5, 4]
  emit directory "v2" .optional .logicalAndConverted [5, 0, 4]
  emit directory "logical" .optional .logical [5, 0, 4]
  emit directory "converted" .optional .converted [5, 0, 4]
  emit directory "required" .required .logicalAndConverted [3, 2]
  for (file, cause) in [
      ("missing", Utf8.Error.missingAnnotation), ("conflict", .convertedType 2),
      ("wrong-logical", .logicalMember 4), ("logical-payload", .logicalPayload)] do
    let bytes ← load directory file
    let .error failed := Utf8.convert {} {} bytes "label" .optional |
      throw (IO.userError s!"unexpected text carrier for {file}")
    unless failed == cause do throw (IO.userError s!"wrong annotation refusal for {file}: {repr failed}")
  let badText ← load directory "bad-text"
  let .ok checked := Utf8.openFile {} badText "label" .optional |
    throw (IO.userError "length-preserving UTF-8 damage should leave the binding intact")
  let .ok first := checked.readGroup {} 0 | throw (IO.userError "first checked group rejected")
  let .ok [] := checked.readGroup {} 1 | throw (IO.userError "explicit empty group rejected")
  unless first == [none, some "", some "é", some "é", some "雪🙂"] do
    throw (IO.userError "nullable ordered prefix changed")
  let refuseWriter : Arrow.MixedFlat.Limits := { observation := { ipc := { fields := 0 } } }
  let .error (.invalidText 2 1) := Utf8.convert {} refuseWriter badText "label" .optional |
    throw (IO.userError "wrong text failure coordinates or writer precedence")
  let .error (.openFile (.fileRowLimit 8 9)) :=
    Utf8.convert { maxFileRows := 8 } {} badText "label" .optional |
    throw (IO.userError "row cap must precede decoding")
  let badLength ← load directory "bad-length"
  let .error (.physical (.page 2 1 "label" 0 offset (.decode (.scalar (.plain .integerOverflow))))) :=
    Utf8.convert {} {} badLength "label" .optional |
    throw (IO.userError "wrong original physical failure")
  unless offset == header do throw (IO.userError "wrong original frame offset")
  let .ok binaryWire := ToIpc.convert {} {} {} badText "label" .optional |
    throw (IO.userError "explicit binary export rejected opaque bytes")
  IO.FS.writeBinFile (directory / "opaque.arrows") binaryWire.toByteArray
  IO.println "Lean: original annotation forms, strict text, typed late failures and opaque export passed"
