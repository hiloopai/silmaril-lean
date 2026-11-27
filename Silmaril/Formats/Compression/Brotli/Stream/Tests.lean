module

import Silmaril.Formats.Compression.Brotli.Stream.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Compression.Brotli.Stream.Defs
meta import Batteries.Data.Except

open Silmaril.Formats.Compression.Brotli (windowSize)
open Silmaril.Formats.Compression.Brotli.Execute (State)
open Silmaril.Formats.Compression.Brotli.Stream

private def limits : Limits := ⟨32, 2, windowSize 24, 256, 4, 17408, 768⟩

-- Two raw blocks separated by nonempty metadata.
private def mixed : List UInt8 := [0, 0, 0x10, 97, 0x56, 0, 90, 91, 0, 0, 8, 98, 3]
private def metadata : List UInt8 := [0xac, 0, 90, 91, 3]

#guard decode {limits with input := mixed.length, bits := 104} mixed =
  .ok { State.start with output := #[97, 98] }
#guard decode {limits with output := 0} metadata = .ok State.start
#guard decode limits [0x5a, 0, 90] = .ok State.start
#guard decode {limits with output := 0, bits := 8, blocks := 1} [0x33] = .ok State.start

#guard decode {limits with input := 12} mixed = .error ⟨0, none, none, .framing .inputLimit⟩
#guard decode {limits with output := 1} mixed = .error ⟨84, some 2, none, .framing .outputLimit⟩
#guard decode {limits with blocks := 3} mixed = .error ⟨96, some 3, none, .framing .stepLimit⟩
#guard decode {limits with bits := 103} mixed = .error ⟨98, some 3, none, .bitLimit⟩
#guard decode {limits with bits := 31} metadata = .error ⟨15, some 0, none, .bitLimit⟩
#guard decode {limits with window := windowSize 16 - 1} mixed = .error ⟨0, none, none, .framing .windowLimit⟩

#guard decode limits [] = .error ⟨0, none, none, .framing .truncated⟩
#guard decode limits [0x11] = .error ⟨0, none, none, .framing .reservedWindow⟩
#guard decode limits [0x1c] = .error ⟨1, some 0, none, .framing .reservedMetadata⟩
#guard decode limits [0x4c, 0, 0] = .error ⟨1, some 0, none, .framing .noncanonicalLength⟩
#guard decode limits [0x04, 0, 0] = .error ⟨1, some 0, none, .framing .noncanonicalLength⟩
#guard decode limits [0xac, 0] = .error ⟨15, some 0, none, .framing .truncated⟩
#guard decode limits [0xac, 0x80, 90, 91, 3] = .error ⟨15, some 0, none, .framing .nonzeroPadding⟩
#guard decode limits [0, 0, 0x30, 97, 3] = .error ⟨21, some 0, none, .framing .nonzeroPadding⟩
#guard decode limits [0x73] = .error ⟨6, some 0, none, .framing .nonzeroPadding⟩
#guard decode limits (mixed ++ [0]) = .error ⟨98, some 3, none, .framing .trailingInput⟩
