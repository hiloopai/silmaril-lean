module

public import Silmaril.Formats.Compression.Bits.Bitstream

/-!
# Bit-level round trip for `LSBWriter` / `LSBReader`

`LSBWriter.Rep w bs` says that the writer `w` holds exactly the bits `bs` (bytes
already flushed, then the partial byte in `buffer`). `LSBReader.Rep r bs` says
that the reader `r` will produce exactly the bits `bs`. Every writer operation
appends to the abstract bit list, every reader operation consumes from its
front, and `toByteArray` / `ofByteArray` connect the two up to zero padding.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

/-- The low `n` bits of `v`, least-significant first. -/
def natBits (v : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => decide (v % 2 = 1) :: natBits (v / 2) n

/-- The low `n` bits of `c`, most-significant first. -/
def msbBits (c : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => c.testBit n :: msbBits c n

/-- The bits of a byte string, each byte least-significant bit first. -/
def bytesBits (bs : List UInt8) : List Bool := bs.flatMap (fun b => natBits b.toNat 8)

/-- The writer `w` holds the bits `bs`. -/
def LSBWriter.Rep (w : LSBWriter) (bs : List Bool) : Prop :=
  w.count < 8 ∧ w.buffer < 2 ^ w.count ∧
    bytesBits w.bytes.data.toList ++ natBits w.buffer w.count = bs

/-- The reader `r` will produce the bits `bs`. -/
def LSBReader.Rep (r : LSBReader) (bs : List Bool) : Prop :=
  r.buffer < 2 ^ r.count ∧ natBits r.buffer r.count ++ bytesBits r.input = bs

end Silmaril.Formats.Compression
