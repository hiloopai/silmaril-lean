module

import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

-- Independently assembled specimen pinned by the libbrotli command trace.
private def specimen : List UInt8 :=
  [0x02, 0x02, 0x80, 0x28, 0x0a, 0x00, 0x84, 0x50, 0x42, 0xa9, 0xa0, 0xa1, 0x16,
   0x40, 0x10, 0x44, 0x20, 0x51, 0x11, 0x49, 0x41, 0x28, 0x0b, 0x93, 0x18]

private def run (header : CompressedHeader.Header) (block : Execute.Block) (output bitCap : Nat) :
    Nat → Execute.InsertCopy.State → LSBReader → Except Execute.DistanceSwitch.Error (Execute.InsertCopy.State × LSBReader)
  | 0, state, cursor => .ok (state, cursor)
  | n + 1, state, cursor => do
    let (next, after) ← read header block ⟨output, bitCap - cursor.totalRead⟩ state cursor
    run header block output bitCap n next.state after

private def check (commands : Nat) (output := 17) (bits := 200) (mlen := 17) (wire := specimen) :
    Option (Except Execute.DistanceSwitch.Error (List UInt8 × Nat × BlockTypes.Switch.Run × Distance.Ring)) := do
  let (window, afterWindow) ← (Brotli.Internal.readWindow (Brotli.Internal.start wire)).toOption
  let (_, tables) ← (Stream.Internal.readHeader afterWindow).toOption
  let (header, payload) ← (CompressedHeader.read ⟨17408, 768, 200 - tables.totalRead⟩ tables).toOption
  return (run header ⟨window, 0, mlen⟩ output bits commands (Execute.InsertCopy.State.start header Execute.State.start)
    payload).map (fun (state, after) =>
      (state.execution.output.toList, after.totalRead, state.runs.distance, state.execution.ring))

#guard check 2 = some (.ok ([65, 67, 65, 67, 65, 67, 65, 67], 183, ⟨0, 1, 0⟩, ⟨2, 4, 11, 15⟩))
#guard check 3 =
  some (.ok ([65, 67, 65, 67, 65, 67, 65, 67, 67, 65, 67, 65], 190, ⟨1, 0, 0⟩, ⟨5, 2, 4, 11⟩))
#guard check 5 =
  some (.ok ([65, 67, 65, 67, 65, 67, 65, 67, 67, 65, 67, 65, 65, 67, 65, 65, 65],
    199, ⟨0, 1, 0⟩, ⟨3, 5, 2, 4⟩))
#guard check 5 (bits := 185) =
  some (.error (.distanceSwitch ⟨185, .distance, .typeSymbol .bitLimit⟩))
#guard check 5 (bits := 187) =
  some (.error (.distanceSwitch ⟨186, .distance, .length .bitLimit⟩))
#guard check 5 (bits := 188) = some (.error (.distance 188 (.symbol .bitLimit)))
#guard check 5 (bits := 189) = some (.error (.distance 188 .extraBitLimit))
#guard check 5 (output := 11) = some (.error (.copy 190 .outputLimit))
#guard check 5 (mlen := 11) (output := 11) = some (.error (.copy 190 .metaBlockExtent))
#guard check 5 (wire := specimen.dropLast) =
  some (.error (.distanceSwitch ⟨192, .distance, .typeSymbol .truncated⟩))
#guard Stream.LiteralSwitch.decode ⟨25, 17, windowSize 16, 200, 1, 17408, 768⟩ specimen =
  .error (.block 0 (.command 0 (.distanceBlockTypes 176)))
