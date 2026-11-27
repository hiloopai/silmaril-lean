module

import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Thms
import Init.Data.Option.Basic
meta import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs
meta import Init.Data.Option.Basic

namespace Silmaril.Formats.Compression.Brotli.Stream.Dictionary

-- Assembled RFC fixture. Prior back-copies establish distance 3; the
-- final compressed block uses it after raw, metadata and dictionary blocks.
private def wire : List UInt8 :=
  [0x00, 0x01, 0x80, 0x28, 0x0a, 0x00, 0x84, 0x50, 0x42, 0xa9, 0xa0, 0xa1, 0x16, 0x40, 0x10,
   0x44, 0x20, 0x51, 0x11, 0x49, 0x41, 0x28, 0x0b, 0x93, 0x18, 0x04, 0x00, 0x04, 0x78, 0x79,
   0x96, 0x00, 0x74, 0x61, 0x67, 0x30, 0x00, 0x40, 0x14, 0x05, 0x00, 0x80, 0x08, 0x0a, 0x41,
   0x62, 0xbd, 0xc0, 0x72, 0x41, 0xc4, 0x00, 0x00, 0x00, 0x88, 0xa0, 0x10, 0x20, 0x20]

private def run (input : List UInt8 := wire) (commands := 8) (output := 30) (blocks := 5) (bits := 472) :
    Except Stream.DistanceSwitch.Error State :=
  decode ⟨⟨input.length, output, windowSize 16, bits, blocks, 17408, 768⟩, commands⟩ input

private def errorOf (result : Except Stream.DistanceSwitch.Error State) : Option Stream.DistanceSwitch.Error :=
  match result with
  | .error reason => some reason
  | .ok _ => none

private def snapshot (result : Except Stream.DistanceSwitch.Error State) :
    Option (List UInt8 × Distance.Ring × Nat) :=
  result.toOption.map fun state => (state.execution.output.toList, state.execution.ring, state.remainingCommands)

#guard snapshot (run) = some ("ACACACACCACAACAAAxytiming ng n".toUTF8.toList, ⟨3, 5, 2, 4⟩, 0)
#guard snapshot (run (commands := 9)) = some ("ACACACACCACAACAAAxytiming ng n".toUTF8.toList, ⟨3, 5, 2, 4⟩, 1)
#guard errorOf (run (commands := 5)) = some (.block 3 (.fuel 0 371))
#guard errorOf (run (commands := 6)) = some (.block 3 (.fuel 1 385))
#guard errorOf (run (commands := 7)) = some (.block 4 (.fuel 0 471))
#guard errorOf (run (bits := 401)) = some (.block 3 (.command 1 (.distance 388 .extraBitLimit)))
#guard errorOf (run (wire.take 50)) = some (.block 3 (.command 1 (.distance 388 .truncatedExtra)))
#guard errorOf (run (blocks := 4)) = some (.envelope ⟨402, some 4, none, .framing .stepLimit⟩)
#guard errorOf (run (output := 29)) = some (.envelope ⟨422, some 4, none, .framing .outputLimit⟩)
#guard errorOf (run (bits := 471)) = some (.envelope ⟨471, some 4, none, .bitLimit⟩)
#guard errorOf (run (wire.set 58 0xa0)) = some (.envelope ⟨471, some 4, none, .framing .nonzeroPadding⟩)
#guard errorOf (run (wire ++ [0xa5]) (bits := 480)) = some (.envelope ⟨471, some 4, none, .framing .trailingInput⟩)
#guard snapshot (run [0x06] (commands := 0) (output := 0) (blocks := 1) (bits := 8)) =
  some ([], Distance.Ring.start, 0)

end Silmaril.Formats.Compression.Brotli.Stream.Dictionary
