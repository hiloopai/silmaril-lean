module

import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Thms
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch

-- Independently assembled two-meta-block wire pinned by the native replay.
private def specimen : List UInt8 :=
  [0x00, 0x01, 0x80, 0x28, 0x0a, 0x00, 0x84, 0x50, 0x42, 0xa9, 0xa0, 0xa1, 0x16,
   0x40, 0x10, 0x44, 0x20, 0x51, 0x11, 0x49, 0x41, 0x28, 0x0b, 0x93, 0x98, 0xa0,
   0x00, 0x20, 0x8a, 0x02, 0x00, 0x21, 0x94, 0x50, 0x2a, 0x68, 0xa8, 0x05, 0x10,
   0x04, 0x11, 0x48, 0x54, 0x44, 0x52, 0x10, 0x0a, 0x0b, 0x93, 0x18]

private def limits : Stream.Limits := ⟨50, 38, windowSize 16, 400, 2, 17408, 768⟩

private def expected : Execute.State :=
  let switched := #[65, 67, 65, 67, 65, 67, 65, 67, 67, 65, 67, 65, 65, 67, 65, 65, 65]
  ⟨switched ++ #[65, 65, 65, 65] ++ switched, ⟨3, 5, 2, 3⟩⟩

#guard decode limits specimen = .ok expected
#guard decode {limits with bits := 385} specimen =
  .error (.block 1 (.command 3 (.distanceSwitch ⟨385, .distance, .typeSymbol .bitLimit⟩)))
#guard decode {limits with bits := 387} specimen =
  .error (.block 1 (.command 3 (.distanceSwitch ⟨386, .distance, .length .bitLimit⟩)))
#guard decode {limits with bits := 389} specimen =
  .error (.block 1 (.command 3 (.distance 388 .extraBitLimit)))
#guard decode limits specimen.dropLast =
  .error (.block 1 (.command 4 (.distanceSwitch ⟨392, .distance, .typeSymbol .truncated⟩)))
#guard decode {limits with output := 37} specimen =
  .error (.envelope ⟨219, some 1, none, .framing .outputLimit⟩)
#guard decode {limits with blocks := 1} specimen =
  .error (.envelope ⟨199, some 1, none, .framing .stepLimit⟩)
#guard decode {limits with bits := 399} specimen =
  .error (.envelope ⟨399, some 1, none, .bitLimit⟩)
#guard decode limits (specimen.dropLast ++ [0x98]) =
  .error (.envelope ⟨399, some 1, none, .framing .nonzeroPadding⟩)
#guard decode {limits with input := 51, bits := 408} (specimen ++ [0]) =
  .error (.envelope ⟨399, some 1, none, .framing .trailingInput⟩)
#guard Stream.LiteralSwitch.decode limits specimen =
  .error (.block 0 (.command 0 (.distanceBlockTypes 176)))
#guard Stream.decode limits specimen = .error ⟨21, some 0, none, .command .blockTypes⟩
#guard decode {limits with input := 1, output := 0, bits := 8, blocks := 1} [6] =
  .ok Execute.State.start
