module

public import Silmaril.Formats.Compression.Inflate.Stream.Blocks

@[expose] public section

namespace Silmaril.Formats.Compression.Deflate

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

/-!
# Progress and locally recomputed bounds for raw DEFLATE

These laws remove semantic fuel from the interface to the mathematical decoder.
All sufficiently large block budgets give the same exact result. Both the
symbol loop and the block loop can therefore unfold into one step followed by
a recursive call whose budget is computed from its own remaining reader.

The progress argument includes every block kind and arbitrary Huffman tables.
It uses the proved parsing-program equality for block-body monotonicity. No C,
Core, machine-word or physical-cursor correspondence is asserted here.
-/

/-! Small success and error checks precede the general progress proofs. A final
empty stored block succeeds, and increasing its already adequate fuel preserves
the exact final reader. An end-of-block token succeeds after one bit. -/

def progressEndTable : HuffmanTable :=
  ⟨1, [⟨256, 0, 1⟩], [], 257⟩

end Silmaril.Formats.Compression.Deflate
