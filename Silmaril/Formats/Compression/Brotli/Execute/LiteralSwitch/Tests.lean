module

import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Stream.Defs
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch

-- Independently assembled and pinned by the native replay.
private def specimen : List UInt8 :=
  [0xa0, 0x00, 0x20, 0x8a, 0x02, 0x10, 0x41, 0x00, 0x10, 0x14, 0x4a, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x80, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x2a, 0x68, 0xa8, 0x80, 0xc1, 0x03, 0x92, 0xc0, 0x24,
   0x20, 0x86, 0x12, 0x8c, 0x50, 0x00, 0x88, 0xa2, 0x00, 0x44, 0x10, 0x00,
   0x04, 0x85, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00,
   0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x0a, 0x1a, 0x2a, 0x60, 0xf0,
   0x80, 0x24, 0x30, 0x09, 0x88, 0xa1, 0x04, 0x03]

private def payload (before : LSBReader) :
    Option (RawLength × CompressedHeader.Header × LSBReader) := do
  let (framing, tables) ← (Stream.Internal.readHeader before).toOption
  let .compressed _ length := framing | none
  let (header, atPayload) ← (CompressedHeader.read ⟨17408, 768, 640 - tables.totalRead⟩ tables).toOption
  return (length, header, atPayload)

private def first (bitCap output : Nat) :
    Option (Except BlockError (List UInt8 × Nat)) := do
  let (window, afterWindow) ← (Brotli.Internal.readWindow (Brotli.Internal.start specimen)).toOption
  let (length, header, reader) ← payload afterWindow
  return (readBlock header window length.size ⟨output, bitCap - reader.totalRead⟩ Execute.State.start reader).map
    (fun (state, after) => (state.execution.output.toList, after.totalRead))

private def blockBytes : List UInt8 := [65, 192, 192, 192, 67, 65, 67, 67, 67, 224, 65]

#guard first 640 22 = some (.ok (blockBytes, 319))
#guard first 299 22 = some (.error (.command 0 (.literal ⟨1, .switch ⟨298, .literal, .length .bitLimit⟩⟩)))
#guard first 300 22 = some (.error (.command 0 (.literal ⟨1, .literal 300 (.symbol .bitLimit)⟩)))
#guard first 302 22 = some (.error (.command 1 (.insertCopySwitch ⟨301, .insertCopy, .length .bitLimit⟩)))
#guard first 296 1 = some (.error (.command 0 (.bounds 296 .outputLimit)))

private def twoBlocks : Option (List UInt8 × Nat) := do
  let (window, afterWindow) ← (Brotli.Internal.readWindow (Brotli.Internal.start specimen)).toOption
  let (length, header, reader) ← payload afterWindow
  let (state, after) ← (readBlock header window length.size ⟨22, 640 - reader.totalRead⟩
    Execute.State.start reader).toOption
  let (length, header, reader) ← payload after
  let (state, after) ← (readBlock header window length.size ⟨22, 640 - reader.totalRead⟩
    state.execution reader).toOption
  return (state.execution.output.toList, after.totalRead)

#guard twoBlocks = some (blockBytes ++ blockBytes, 637)
