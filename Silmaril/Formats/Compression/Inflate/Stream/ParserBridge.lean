module

public import Silmaril.Formats.Compression.Inflate.Stream.ParserPhases

/-!
# Streaming phase observations, resumption and contract transport

The resumable parsers are related to the existing
mathematical DEFLATE phases for every scheduler budget and every later input
extension. `resume` supports repeated chunk delivery and scheduler yields.
The executable witnesses exercise partial LEN/NLEN reads and a nine-bit Huffman
code, rather than assuming entire phases complete before suspension.

The logical reader normalizes prefetched bytes. None of these theorems asserts
that its cursor equals zlib's physical C cursor, or supplies a C/Core, packed
lookup-table, word-overflow, allocation or full streaming-API correspondence.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

/-- Resume only incomplete programs. Completed/error results retain their
observation and frame the newly supplied input in the reservoir. -/
def RunResult.resume {α : Type} (result : RunResult α) (fuel : Nat)
    (added : List UInt8) : RunResult α :=
  match result with
  | .done value state => .done value (state.feed added)
  | .error err state => .error err (state.feed added)
  | .needInput continuation state | .yield continuation state =>
    Parser.run fuel continuation (state.feed added)

namespace ParserBridge

/-- Reassociate the table pair and reader without dropping any error or field. -/
def dynamicTablesSpec (reader : LSBReader) :
    Except Deflate.DecompressError ((HuffmanTable × HuffmanTable) × LSBReader) :=
  match Deflate.readDynamicTables reader with
  | .error err => .error err
  | .ok (literals, distances, rest) => .ok ((literals, distances), rest)

/-! ## Kernel-checked split-input executions -/

def headerLenPrefix : RunResult Nat :=
  Parser.run 8 ParserPhases.storedHeader (Reservoir.ofBytes [3])

def headerNlenPrefix : RunResult Nat := headerLenPrefix.resume 8 [0, 0xfc]

def headerYield : RunResult Nat :=
  Parser.run 1 ParserPhases.storedHeader (Reservoir.ofBytes [3, 0, 0xfc, 0xff])

/-- A single supplied code isolates a nine-bit literal's continuation. The
entry is the fixed alphabet's code for literal 144; this small witness table
is not asserted to be the entire fixed DEFLATE alphabet. -/
def longLiteralTable : HuffmanTable :=
  { maxBits := 9, entries := [⟨144, 400, 9⟩], symbolCodes := [], alphabetSize := 256 }

def tokenPrefix : RunResult Manual.Token :=
  Parser.run 32 (ParserPhases.token longLiteralTable (HuffmanTable.empty 0))
    (Reservoir.ofBytes [0x13])

end ParserBridge
end Silmaril.Formats.Compression.Inflate.Stream
