module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedReservoir

/-!
# Complete buffered fixed-code operations

The canonical operation reads a Huffman symbol and
then that symbol's extra bits. The packed operation independently indexes the
source tables. With enough buffered bits their complete value/failure behavior
agrees, the final reservoir normalizes the canonical reader, and the exact
physical state is obtained solely by dropping code and extra bits: no source
input byte is pulled. Thirteen buffered bits suffice for every fixed
literal/length operation; eighteen suffice for every fixed distance operation.

Reserved codes explicitly fail. This is one operation, not yet the composition
of a length operation and a distance operation into a token, and not C execution.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def extraWidth : Meaning → Nat
  | .baseExtra _ bits => bits
  | _ => 0

/-- The mathematical Huffman reader followed by interpretation of its symbol.
Failure is explicit, including a successfully read reserved symbol. -/
def canonicalOperation (table : HuffmanTable) (interpret : Nat → Meaning)
    (reader : LSBReader) : Option (Value × LSBReader) :=
  match table.readSymbolLSB reader with
  | none => none
  | some (symbol, rest) => finishMeaning (interpret symbol) rest

/-- Value correspondence retains the complete canonical reader. Both result
forms retain the exact physical drop state, ruling out hidden source refill. -/
def DecodeCorrespondence (before : Reservoir) (canonical : Option (Value × LSBReader)) :
    DecodeResult → Prop
  | .value value after code extra =>
    ∃ reader, canonical = some (value, reader) ∧ Reservoir.Normalizes after reader ∧
      after = before.dropBits (code + extra)
  | .invalid after code =>
    canonical = none ∧ after = before.dropBits code ∧ after.Valid
  | _ => False

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
