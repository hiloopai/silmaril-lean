module

public import Silmaril.Formats.Compression.Inflate.Stream.RawRuns

/-!
# Reader positions and container composition

The absolute bit-position counter records consumed headers but never affects
parsing decisions. Shifting it commutes with every read/align program and the
shared raw decoder. Container payloads can therefore enter raw decoding at
their actual position without resetting the physical input cursor.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset

open Silmaril.Formats.Compression

def shift (offset : Nat) (reader : LSBReader) : LSBReader :=
  { reader with totalRead := reader.totalRead + offset }

end Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset
