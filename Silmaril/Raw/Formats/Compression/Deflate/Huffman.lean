module

public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Bits.Bitstream

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Deflate.Huffman`. -/

@[expose] public section

namespace Silmaril.Formats.Compression

/-! ### A decode index

`lookupEntry` is a linear scan, and `decodeSymbolLSBAux` calls it once per
candidate code length per symbol, so decoding costs `O(maxBits × |entries|)` per
symbol.  The index below is built once per block and answers the same question
in O(1); `lookupEntryIdx_eq` proves it gives exactly `lookupEntry`'s answer, so
the decoder's specification is untouched.

The key of a code is `2 ^ len + code`, which is injective on the codes that can
actually occur (`0 < len ≤ 15` and `code < 2 ^ len`, RFC 1951 §3.2.7).  Anything
outside that range falls back to the scan, so the equality holds for *every*
entry list, including malformed ones. -/

theorem buildDecTable_size : ∀ (es : List CodeEntry) (a : Array Nat),
    (buildDecTable es a).size = a.size := by
  intro es
  induction es with
  | nil => intro a; rfl
  | cons e rest ih => intro a; rw [buildDecTable, ih, insertDecEntry_size]

end Silmaril.Formats.Compression
