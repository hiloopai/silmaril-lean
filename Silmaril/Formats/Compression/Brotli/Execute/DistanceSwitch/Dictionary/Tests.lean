module

import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Thms
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open Silmaril.Formats.Compression

private def header (code : Nat) (fits : code < 64 := by decide) (command : Fin 704 := 130) :
    CompressedHeader.Header :=
  ⟨⟨⟨.single, .single, .single⟩, ⟨0, 0, [.lsb6]⟩⟩, .implicit 64, .implicit 4,
    [.singleton 256 65 (by decide)], [.singleton 704 command.val command.isLt], [.singleton 64 code fits]⟩

private def cursor (bits : List Bool) : LSBReader :=
  let width := bits.length % 8
  let lead := LSBWriter.empty.writeBits (bits.take width)
  let bytes := LSBWriter.empty.writeBits (bits.drop width)
  ⟨lead.buffer, lead.count, bytes.bytes.data.toList, 11⟩

private def run (header : CompressedHeader.Header) (bits : List Bool) (mlen output bitCap : Nat) :
    Except DistanceSwitch.Error (InsertCopy.Result × LSBReader) :=
  read header ⟨18, 0, mlen⟩ ⟨output, bitCap⟩ (InsertCopy.State.start header Execute.State.start) (cursor bits)

private def observed (result : Except DistanceSwitch.Error (InsertCopy.Result × LSBReader)) :
    Option (List UInt8 × Nat × Nat × Distance.Ring × Option Bool) := do
  let (step, after) ← result.toOption
  pure (step.execution.state.output.toList, step.execution.command.copyLength, after.totalRead,
    step.execution.state.ring, after.readBit |>.map Prod.fst)

private def errorOf (result : Except DistanceSwitch.Error (InsertCopy.Result × LSBReader)) :
    Option DistanceSwitch.Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

-- Dictionary word 0 of length 4 is "time". Transform 1 adds one byte.
#guard observed (run (header 32) (natBits 4 9 ++ [true]) 5 5 9) =
  some ([116, 105, 109, 101, 32], 4, 20, Distance.Ring.start, some true)
#guard errorOf (run (header 32) (natBits 4 9) 4 4 9) = some (.copy 20 .metaBlockExtent)
#guard errorOf (run (header 32) (natBits 4 9) 5 4 9) = some (.copy 20 .outputLimit)
#guard errorOf (run (header 32) (natBits 4 9) 5 5 8) = some (.distance 11 .extraBitLimit)
#guard errorOf (run (header 32) (natBits 4 8) 5 5 9) = some (.distance 11 .truncatedExtra)

-- Transform 12 omits one byte. An empty transformed word still consumes
-- its original distance bits and retains the incoming state.
#guard observed (run (header 39) (natBits 4 12) 3 3 12) =
  some ([116, 105, 109], 4, 23, Distance.Ring.start, none)
#guard observed (run (header 43) (natBits 6148 14 ++ [false]) 1 1 14) =
  some ([], 4, 25, Distance.Ring.start, some false)

-- The first invalid dictionary ordinal, and a command with a base length of two.
#guard errorOf (run (header 45) (natBits 25604 15) 5 5 15) = some (.distance 11 .dictionaryWord)
#guard errorOf (run (header 16 (command := 128)) [false] 5 5 1) = some (.distance 11 .dictionaryLength)

#guard (
  let tables := header 32
  let block : Execute.Block := ⟨18, 0, 10⟩
  let limits : Execute.Limits := ⟨10, 18⟩
  let before := cursor (natBits 4 9 ++ natBits 9 9 ++ [false])
  let paired := do
    let (first, next) ← read tables block limits (InsertCopy.State.start tables Execute.State.start) before
    read tables block { limits with bits := limits.bits - (next.totalRead - before.totalRead) } first.state next
  observed paired) = some ([116, 105, 109, 101, 32, 116, 105, 109, 101, 32], 4, 29,
    Distance.Ring.start, some false)

#guard errorOf (DistanceSwitch.read (header 32) ⟨18, 0, 5⟩ ⟨5, 9⟩
    (InsertCopy.State.start (header 32) Execute.State.start) (cursor (natBits 4 9))) =
  some (.copy 20 (.unsupportedDictionary 1025 4 1024))

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
