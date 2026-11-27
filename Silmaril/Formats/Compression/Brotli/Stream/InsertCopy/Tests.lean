module

import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Stream.InsertCopy

-- Independently assembled fixture pinned by the native whole-stream replay.
private def fixture : List UInt8 :=
  [0x30, 0x01, 0x40, 0x24, 0x1d, 0x20, 0x04, 0x54, 0x90, 0x50, 0x20, 0x12,
   0x02, 0x04, 0xc4, 0x80, 0x89, 0x96, 0x00, 0x74, 0x61, 0x67, 0xd1, 0x00,
   0x20, 0x82, 0x00, 0x20, 0xa0, 0x82, 0x84, 0x42, 0x80, 0x40, 0x24, 0x20,
   0x09]

private def limits : Stream.Limits := ⟨37, 34, windowSize 16, 296, 3, 17408, 768⟩
private def output : Execute.State :=
  ⟨#[0x41, 0x41, 0x41, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x41, 0x41,
    0x41, 0x41, 0x41, 0x41, 0x41, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42,
    0x41, 0x41, 0x41, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42, 0x42], ⟨1, 1, 1, 1⟩⟩

#guard decode limits fixture = .ok output
#guard Stream.decode limits fixture = .error ⟨21, some 0, none, .command .blockTypes⟩
#guard decode {limits with bits := 120} fixture =
  .error (.command 0 2 (.switch ⟨119, .insertCopy, .typeSymbol .bitLimit⟩))
#guard decode {limits with bits := 289} fixture =
  .error (.command 2 1 (.switch ⟨288, .insertCopy, .length .bitLimit⟩))
#guard decode limits fixture.dropLast =
  .error (.command 2 1 (.switch ⟨288, .insertCopy, .length .truncated⟩))
#guard decode {limits with bits := 290} fixture =
  .error (.command 2 1 (.execute 290 (.literal (.symbol .bitLimit))))
#guard decode {limits with blocks := 2} fixture =
  .error (.envelope ⟨176, some 2, none, .framing .stepLimit⟩)
#guard decode {limits with bits := 295} fixture =
  .error (.envelope ⟨294, some 2, none, .bitLimit⟩)
