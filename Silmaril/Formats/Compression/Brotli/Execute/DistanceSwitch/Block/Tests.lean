module

import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Thms
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

-- Independently assembled two-meta-block stream pinned by the native replay.
private def specimen : List UInt8 :=
  [0x00, 0x01, 0x80, 0x28, 0x0a, 0x00, 0x84, 0x50, 0x42, 0xa9, 0xa0, 0xa1, 0x16,
   0x40, 0x10, 0x44, 0x20, 0x51, 0x11, 0x49, 0x41, 0x28, 0x0b, 0x93, 0x98, 0xa0,
   0x00, 0x20, 0x8a, 0x02, 0x00, 0x21, 0x94, 0x50, 0x2a, 0x68, 0xa8, 0x05, 0x10,
   0x04, 0x11, 0x48, 0x54, 0x44, 0x52, 0x10, 0x0a, 0x0b, 0x93, 0x18]

private def decoded : List UInt8 :=
  [65, 67, 65, 67, 65, 67, 65, 67, 67, 65, 67, 65, 65, 67, 65, 65, 65]

private def runPayload (window output bits : Nat) (initial : Execute.State) (before : LSBReader) :
    Option (Except BlockError (Execute.InsertCopy.State × LSBReader)) := do
  let (framing, tables) ← (Stream.Internal.readHeader before).toOption
  let .compressed _ length := framing | none
  let (header, body) ← (CompressedHeader.read ⟨17408, 768, 400 - tables.totalRead⟩ tables).toOption
  return readBlock header window length.size ⟨output, bits - body.totalRead⟩ initial body

private def first : Option (List UInt8 × Nat × Nat × Distance.Ring) := do
  let (window, reader) ← (Brotli.Internal.readWindow (Brotli.Internal.start specimen)).toOption
  let (state, after) ← (← runPayload window 38 400 Execute.State.start reader).toOption
  let (flags, _) ← after.readBits 2
  return (state.execution.output.toList, after.totalRead, flags, state.execution.ring)

private def second (output := 38) (bits := 400) (wire := specimen) :
    Option (Except BlockError (List UInt8 × Nat × Distance.Ring × BlockTypes.Switch.Run)) := do
  let (window, reader) ← (Brotli.Internal.readWindow (Brotli.Internal.start wire)).toOption
  let (state, after) ← (← runPayload window 38 400 Execute.State.start reader).toOption
  return (← runPayload window output bits state.execution after).map (fun (next, stop) =>
    (next.execution.output.toList, stop.totalRead, next.execution.ring, next.runs.distance))

#guard first = some (decoded, 199, 1, ⟨3, 5, 2, 4⟩)
#guard second = some (.ok (decoded ++ [65, 65, 65, 65] ++ decoded, 399, ⟨3, 5, 2, 3⟩, ⟨0, 1, 0⟩))
#guard second (bits := 385) =
  some (.error (.command 3 (.distanceSwitch ⟨385, .distance, .typeSymbol .bitLimit⟩)))
#guard second (bits := 387) =
  some (.error (.command 3 (.distanceSwitch ⟨386, .distance, .length .bitLimit⟩)))
#guard second (bits := 388) = some (.error (.command 3 (.distance 388 (.symbol .bitLimit))))
#guard second (output := 32) = some (.error (.command 3 (.copy 390 .outputLimit)))
#guard second (output := 16) = some (.error (.initialOutput 374))
#guard second (wire := specimen.dropLast) =
  some (.error (.command 4 (.distanceSwitch ⟨392, .distance, .typeSymbol .truncated⟩)))
#guard Stream.LiteralSwitch.decode ⟨50, 38, windowSize 16, 400, 2, 17408, 768⟩ specimen =
  .error (.block 0 (.command 0 (.distanceBlockTypes 176)))
