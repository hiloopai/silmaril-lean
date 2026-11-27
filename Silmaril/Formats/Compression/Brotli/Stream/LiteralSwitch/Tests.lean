module

import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch

-- RFC assembly with raw, metadata, two L/I-switched blocks and a cross-block copy.
private def mixed : List UInt8 :=
  [0x10, 0x00, 0x10, 0x78, 0x79, 0x96, 0x00, 0x74, 0x61, 0x67, 0x50, 0x00,
   0x10, 0x45, 0x01, 0x88, 0x20, 0x00, 0x08, 0x0a, 0x25, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x15, 0x34, 0x54, 0xc0, 0xe0, 0x01, 0x49, 0x60, 0x12, 0x10, 0x43,
   0x09, 0x06, 0x14, 0x00, 0x44, 0x51, 0x00, 0x22, 0x08, 0x00, 0x82, 0x42,
   0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x10, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x40, 0x05, 0x0d, 0x15, 0x30, 0x78, 0x40, 0x12,
   0x98, 0x04, 0xc4, 0x50, 0x82, 0x11, 0x03, 0x00, 0x20, 0x20, 0x00, 0x42,
   0x80, 0x80, 0x00]

private def limits : Stream.Limits := ⟨99, 28, windowSize 16, 792, 5, 17408, 768⟩

private def expected : Execute.State :=
  let switched := #[65, 192, 192, 192, 67, 65, 67, 67, 67, 224, 65]
  ⟨#[120, 121] ++ switched ++ switched ++ #[65, 65, 65, 65], ⟨1, 1, 1, 1⟩⟩

#guard decode limits mixed = .ok expected
#guard decode {limits with bits := 696} mixed =
  .error (.block 3 (.command 0 (.literal ⟨1, .switch ⟨695, .literal, .length .bitLimit⟩⟩)))
#guard decode {limits with bits := 699} mixed =
  .error (.block 3 (.command 1 (.insertCopySwitch ⟨698, .insertCopy, .length .bitLimit⟩)))
#guard decode {limits with output := 27} mixed =
  .error (.envelope ⟨736, some 4, none, .framing .outputLimit⟩)
#guard decode {limits with blocks := 4} mixed =
  .error (.envelope ⟨716, some 4, none, .framing .stepLimit⟩)
#guard decode {limits with bits := 791} mixed =
  .error (.envelope ⟨786, some 4, none, .bitLimit⟩)
#guard decode limits (mixed.dropLast ++ [0x04]) =
  .error (.envelope ⟨786, some 4, none, .framing .nonzeroPadding⟩)
#guard decode {limits with input := 100, bits := 800} (mixed ++ [0]) =
  .error (.envelope ⟨786, some 4, none, .framing .trailingInput⟩)
#guard decode {limits with input := 1, output := 0, bits := 8, blocks := 1} [6] =
  .ok Execute.State.start
