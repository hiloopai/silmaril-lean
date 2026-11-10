module

public import Silmaril.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Formats.Compression.Bits.Bit
public import Silmaril.Formats.Compression.Bits.Bitstream
public import Silmaril.Formats.Compression.Deflate.Huffman
public import Silmaril.Formats.Compression.Deflate.Decompress
public import Silmaril.Formats.Compression.Deflate.Stored
public import Silmaril.Formats.Compression.Deflate.WithHistory
public import Silmaril.Formats.Compression.Deflate.Compress
public import Silmaril.Formats.Compression.Deflate.LZ77
public import Silmaril.Formats.Compression.Bits.ByteFields
public import Silmaril.Formats.Compression.Checksum.Adler32
public import Silmaril.Formats.Compression.Checksum.CRC32
public import Silmaril.Formats.Compression.Zlib.Basic
public import Silmaril.Formats.Compression.Zlib.Take
public import Silmaril.Formats.Compression.Zlib.Dictionary
public import Silmaril.Formats.Compression.Gzip.Basic

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

namespace Parser

end Parser

namespace Blocks

/-!
# Resumable raw DEFLATE block programs

Independently expressed parsing programs for the
two pinned versions' shared abstract block algorithm. Canonical evaluation
agrees with the existing mathematical decoder, including fixed and dynamic
Huffman blocks, overlapping matches, stored blocks, and every parse error.

The symbol budget is fixed before streaming starts. An adequate budget may be
chosen from a known upper bound on the complete input's bit length. Scheduler
fuel is independent and may yield at any point. These programs stream input;
they retain complete logical output and do not implement zlib's output buffer,
packed tables, fast loop, physical cursor protocol, or C/Core execution.
-/

def storedBody (output : List UInt8) : Parser (List UInt8) :=
  ParserPhases.stored.bind fun bytes => .pure (output ++ bytes)

def fixedBody (symbolBudget : Nat) (output : List UInt8) : Parser (List UInt8) :=
  match Deflate.fixedLitLenTable, Deflate.fixedDistTable with
  | some litLen, some dist => ParserPhases.symbols litLen dist symbolBudget output
  | _, _ => .fail .badFixedTable

def dynamicBody (symbolBudget : Nat) (output : List UInt8) : Parser (List UInt8) :=
  ParserPhases.dynamicTables.bind fun tables =>
    ParserPhases.symbols tables.1 tables.2 symbolBudget output

def body131 (symbolBudget kind : Nat) (output : List UInt8) : Parser (List UInt8) :=
  if kind = 0 then storedBody output
  else if kind = 1 then fixedBody symbolBudget output
  else if kind = 2 then dynamicBody symbolBudget output
  else .fail (.badBlockType kind)

def bodyDevelop (symbolBudget : Nat) (kind : Nat) (output : List UInt8) :
    Parser (List UInt8) :=
  match kind with
  | 0 => storedBody output
  | 1 => fixedBody symbolBudget output
  | 2 => dynamicBody symbolBudget output
  | other => .fail (.badBlockType other)

/-- BFINAL and BTYPE retain their partial read on suspension. -/
def header : Parser (Bool × Nat) :=
  .bits 1 .decodeOverrun fun final =>
    .bits 2 .decodeOverrun fun kind => .pure (decide (final ≠ 0), kind)

def blocks (body : Nat → List UInt8 → Parser (List UInt8)) :
    Nat → List UInt8 → Parser (List UInt8)
  | 0, _ => .fail .decodeOverrun
  | fuel + 1, output => header.bind fun parsed =>
    (body parsed.2 output).bind fun next =>
      if parsed.1 then .pure next else blocks body fuel next

def program131 (budget : Nat) (output : List UInt8) : Parser (List UInt8) :=
  blocks (body131 budget) budget output

def programDevelop (budget : Nat) (output : List UInt8) : Parser (List UInt8) :=
  blocks (bodyDevelop budget) budget output

def inputView (result : Except Deflate.DecompressError (List UInt8 × LSBReader)) :
    Except Deflate.DecompressError (List UInt8 × List UInt8) :=
  result.map fun pair => (pair.1, pair.2.input)

def initialReader (bytes : List UInt8) : LSBReader := ⟨0, 0, bytes, 0⟩
def inputBudget (bytes : List UInt8) : Nat := 8 * bytes.length + 1

def take131 (bytes : List UInt8) : Except Deflate.DecompressError (List UInt8 × List UInt8) :=
  inputView ((program131 (inputBudget bytes) []).eval (initialReader bytes))

def takeDevelop (bytes : List UInt8) : Except Deflate.DecompressError (List UInt8 × List UInt8) :=
  inputView ((programDevelop (inputBudget bytes) []).eval (initialReader bytes))

end Blocks

/-- Feed any finite sequence of chunks, preserving each retained continuation.
An exhausted scheduler budget yields, so even empty chunks may be useful. -/
def RunResult.resumeChunks {α : Type} (result : RunResult α) (schedulerFuel : Nat) :
    List (List UInt8) → RunResult α
  | [] => result
  | chunk :: chunks => (result.resume schedulerFuel chunk).resumeChunks schedulerFuel chunks

namespace Blocks

/-! Kernel-reduced witnesses: LEN and NLEN are split across input deliveries,
and a non-final empty block exercises the recursive block-header loop. -/

def storedPrefix : RunResult (List UInt8) :=
  Parser.run 128 (program131 65 []) (Reservoir.ofBytes [1, 3])

end Blocks
end Silmaril.Formats.Compression.Inflate.Stream
