module

import Lean
import Silmaril.Formats.Parquet.ScalarPage.Brotli.Defs
meta import Silmaril.Formats.Parquet.ScalarPage.Brotli.Defs

open Lean Silmaril.Formats Silmaril.Formats.Parquet
open ScalarPage.Brotli (Error decodeAt)

private def requireIO {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def failure (error : Error) : Json :=
  match error with
  | .codec id => Json.mkObj [("error", "codec"), ("actual", toJson id)]
  | .checksum (.mismatch declared computed) =>
    Json.mkObj [("error", "checksum"), ("declared", toJson declared.toNat), ("computed", toJson computed.toNat)]
  | .checksum .byteLimit => Json.mkObj [("error", "storedCap")]
  | .page (.payload .outputLimit) => Json.mkObj [("error", "outputCap")]
  | .page (.payload .outputSizeMismatch) => Json.mkObj [("error", "expandedSize")]
  | .framing (.header .invalidV2Lengths) => Json.mkObj [("error", "v2Lengths")]
  | .stream (.envelope ⟨bit, _, _, .framing .trailingInput⟩) =>
    Json.mkObj [("error", "trailingStream"), ("bit", toJson bit)]
  | .stream (.envelope ⟨bit, _, _, .framing .windowLimit⟩) =>
    Json.mkObj [("error", "windowCap"), ("bit", toJson bit)]
  | .stream (.block block (.fuel command bit)) =>
    Json.mkObj [("error", "commandCap"), ("block", toJson block), ("command", toJson command), ("bit", toJson bit)]
  | .stream (.block block (.command command (.distance bit .truncatedExtra))) =>
    Json.mkObj [("error", "truncatedDistance"), ("block", toJson block), ("command", toJson command), ("bit", toJson bit)]
  | .stream reason => Json.mkObj [("error", "stream"), ("cause", toJson (reprStr reason))]
  | _ => Json.mkObj [("error", "other"), ("cause", toJson (reprStr error))]

private def locate (mode : String) (source : Bytes) : IO (FlatColumn.Layout × Int × Footer.Span) := do
  if mode = "page" then return (.optional, 4, ⟨0, source.length⟩)
  let file ← requireIO (Snapshot.check (Failure := Unit) {} source)
  let some group := file.groupAt 0 | throw (IO.userError "missing row group")
  let [column] := group.columns | throw (IO.userError "expected one column")
  let some leaf := file.metadata.schema[1]? | throw (IO.userError "missing leaf")
  let layout ← match leaf.repetition with
    | some .required => pure FlatColumn.Layout.required
    | some .optional => pure FlatColumn.Layout.optional
    | _ => throw (IO.userError "expected flat layout")
  let some span := Page.columnSpan file.footer.start column.metadata | throw (IO.userError "invalid chunk")
  return (layout, column.metadata.codec, span)

public def main (args : List String) : IO UInt32 := do
  let [path, mode, comp, plain, window, bits, blocks, commands, requested] := args | return 2
  let (some storedCap, some outputCap, some windowCap, some bitCap, some blockCap, some commandCap, some codec) :=
    (comp.toNat?, plain.toNat?, window.toNat?, bits.toNat?, blocks.toNat?, commands.toNat?, requested.toInt?) |
    return 2
  let source : Bytes := ⟨← IO.FS.readBinFile path⟩
  let (layout, footerCodec, span) ← locate mode source
  let limits : ScalarPage.Brotli.Limits := {
    framing := {}, page := ⟨storedCap, outputCap, ⟨262144, 1048576⟩, 0⟩
    window := windowCap, bits := bitCap, blocks := blockCap, commands := commandCap }
  let codec := if codec = -1 then footerCodec else codec
  match decodeAt limits layout codec source span span.start with
  | .error error => IO.println (failure error).compress
  | .ok result =>
    let frame := result.frame
    let checked := match result.checksum with
      | .absent => none
      | .valid crc => some crc.toNat
    let stored := Page.Checksum.payloadBytes source frame
    let sizes : ScalarPage.Sizes := ⟨frame.value.compressedSize, frame.value.uncompressedSize⟩
    let strict := match Payload.decode (limits.page.payloadBounds sizes 0) codec stored.toList with
      | .error (.unsupportedCodec 4) => true
      | _ => false
    IO.println (Json.mkObj [("header", toJson [frame.header.start, frame.header.stop]),
      ("payload", toJson [frame.payload.start, frame.payload.stop]), ("crc", toJson checked),
      ("expanded", toJson (result.expanded.map UInt8.toNat)), ("legacyRefused", toJson strict)]).compress
  return 0
