module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedTableEntry

/-!
# Logical bit effects of packed Huffman lookup

A successful root or root/subtable lookup performs
exactly one bounded logical code-bit read. The two physical DROPBITS operations
on the subtable path are related to that single read, including the entire
remaining bitstream and its canonical-reader normalization. Extra-bit decoding
can then compose with this edge independently of the chosen table.

These theorems establish consumption and representation, not the meaning of a
Huffman codebook. The separate fixed-table correspondence checks code meanings;
dynamic table construction, refilling the lookup's code bits, packed memory and
C/Core/machine execution still require their own refinements.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

/-- Interpret an already selected operation using the canonical bit reader.
Selecting the operation itself is the independent codebook obligation. -/
def finishMeaning (selected : Meaning) (reader : LSBReader) : Option (Value × LSBReader) :=
  match selected with
  | .literal value => some (.literal value, reader)
  | .endBlock => some (.endBlock, reader)
  | .invalid => none
  | .baseExtra base extra =>
    (reader.readBits extra).map fun (amount, rest) => (.amount (base + amount), rest)

/-! Small satisfiable branch checks: a one-bit
root plus a one-bit leaf consumes two bits, while the same root with only one
available bit suspends without consuming it. -/

def checkedLinked : Array Entry :=
  #[⟨0, 1, 65⟩, ⟨1, 1, 2⟩, ⟨0, 1, 66⟩, ⟨0, 1, 67⟩]

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
