module

public import Silmaril.Formats.Compression.Deflate.Stored

/-!
# Raw DEFLATE with initial history

The existing decoder already accepts a logical
history prefix. Its dictionary-aware observation returns only bytes generated
after that prefix and the untouched byte suffix after the final block. As in
`deflateTake`, any final partial-byte padding disappears from the observation.

This is a shared mathematical specification, independent of a C implementation
or calling protocol. It neither validates a dictionary identifier nor chooses
the installed window suffix; a zlib wrapper must do those separately. In the
32 KiB profile, the supplied history is the final 32768 dictionary bytes.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

/-- Observe a seeded decoder result as newly generated data and remaining
whole bytes. The initial logical history is not returned as decompressed data. -/
def resultWithHistory (history : List UInt8)
    (result : Except DecompressError (List UInt8 × LSBReader)) :
    Except DecompressError (List UInt8 × List UInt8) :=
  result.map fun pair => (pair.1.drop history.length, pair.2.input)

/-- Decode one raw DEFLATE stream with an installed history. History affects
back-references but does not count towards returned data. The final unread
whole bytes remain available to the container's trailer parser. -/
def deflateTakeWithHistory (history input : List UInt8) :
    Except DecompressError (List UInt8 × List UInt8) :=
  let reader : LSBReader := ⟨0, 0, input, 0⟩
  resultWithHistory history (decompressBlocks (reader.bitsLeft + 1) reader history)

end Silmaril.Formats.Compression.Deflate
