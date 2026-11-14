module

public import Silmaril.Proofs.Formats.Compression.DeflateSpec.Sound

/-!
# Known answers

The zlib vectors of `Deflate.Thms` (`kat_stored`, `kat_fixed`, `kat_dynamic`)
satisfy `DeflateSpec.Stream`, and the spec's own definitions reproduce the
worked examples of RFC 1951.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression.DeflateSpec

open Silmaril.Formats.Compression Silmaril.Formats.Compression.Deflate

set_option maxRecDepth 100000 in
theorem deflateTake_stored_vector :
    deflateTake [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63] = .ok ([0x61, 0x62, 0x63], []) := by
  rfl

set_option maxRecDepth 100000 in
theorem deflateTake_fixed_vector :
    deflateTake [0x4b, 0x4c, 0x4a, 0x06, 0x00] = .ok ([0x61, 0x62, 0x63], []) := by
  rfl

set_option maxRecDepth 100000 in
theorem deflateTake_dynamic_vector :
    deflateTake [0x25, 0x88, 0xb1, 0x09, 0x00, 0x00, 0x0c, 0x83, 0x6e, 0x35, 0xe6, 0xff,
      0x1b, 0x1a, 0xa8, 0x83, 0x88, 0xd8, 0x02, 0xd5, 0xe0, 0x82, 0x7c, 0x4e, 0x1d, 0xd8,
      0xb8, 0xe3, 0x01] =
      .ok ([0x61, 0x63, 0x64, 0x64, 0x61, 0x61, 0x61, 0x64, 0x63, 0x63, 0x62, 0x61,
        0x63, 0x61, 0x61, 0x61, 0x61, 0x62, 0x64, 0x63, 0x63, 0x62, 0x61, 0x63, 0x63,
        0x63, 0x62, 0x64, 0x64, 0x64, 0x64, 0x61, 0x63, 0x64, 0x62, 0x63, 0x64, 0x63,
        0x63, 0x63], []) := by
  rfl

set_option maxRecDepth 100000 in
theorem fixedLitLenCode_table :
    DeflateSpec.fixedLitLenCode 0 = some (DeflateSpec.codeBits 0b00110000 8) ∧
    DeflateSpec.fixedLitLenCode 143 = some (DeflateSpec.codeBits 0b10111111 8) ∧
    DeflateSpec.fixedLitLenCode 144 = some (DeflateSpec.codeBits 0b110010000 9) ∧
    DeflateSpec.fixedLitLenCode 255 = some (DeflateSpec.codeBits 0b111111111 9) ∧
    DeflateSpec.fixedLitLenCode 256 = some (DeflateSpec.codeBits 0b0000000 7) ∧
    DeflateSpec.fixedLitLenCode 279 = some (DeflateSpec.codeBits 0b0010111 7) ∧
    DeflateSpec.fixedLitLenCode 280 = some (DeflateSpec.codeBits 0b11000000 8) ∧
    DeflateSpec.fixedLitLenCode 287 = some (DeflateSpec.codeBits 0b11000111 8) ∧
    DeflateSpec.fixedLitLenCode 288 = none := by
  decide

theorem ofLengths_example :
    (List.range 8).map (DeflateSpec.Code.ofLengths [3, 3, 3, 3, 3, 2, 4, 4]) =
      [some [false, true, false], some [false, true, true], some [true, false, false],
       some [true, false, true], some [true, true, false], some [false, false],
       some [true, true, true, false], some [true, true, true, true]] := by
  decide

theorem copyMatch_example (x y : UInt8) :
    DeflateSpec.copyMatch [x, y] 2 5 = [x, y, x, y, x, y, x] := rfl

end Silmaril.Proofs.Formats.Compression.DeflateSpec
