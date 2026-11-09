module

public import Silmaril.Formats.Compression.Inflate.Stream.Bits
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

/-!
# Resumable bit-reading programs

A small mathematical interpreter separating parsing
control flow from physical bit buffering. `eval` uses the canonical format
reader. `run` uses the source-like reservoir and retains the exact continuation
and partial refill on suspension. Its fuel bounds interpreter transitions, and
exhaustion yields a resumable continuation rather than a format error.

`run_correct_feed` relates every result to canonical evaluation, including after
any later input extension. This is a compositional parsing layer, not a C/Core
semantics, machine-word theorem, output allocator or complete inflater API.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream

open Silmaril.Formats.Compression

inductive Parser (α : Type) where
  | pure (value : α)
  | fail (error : Deflate.DecompressError)
  | bits (count : Nat) (eofError : Deflate.DecompressError) (next : Nat → Parser α)
  | align (next : Parser α)

namespace Parser

def bind {α β : Type} : Parser α → (α → Parser β) → Parser β
  | .pure value, next => next value
  | .fail error, _ => .fail error
  | .bits count error continuation, next =>
    .bits count error (fun value => bind (continuation value) next)
  | .align continuation, next => .align (bind continuation next)

def readBits (count : Nat) (eofError : Deflate.DecompressError) : Parser Nat :=
  .bits count eofError .pure

def alignToByte : Parser Unit := .align (.pure ())

def eval {α : Type} : Parser α → LSBReader → Except Deflate.DecompressError (α × LSBReader)
  | .pure value, reader => .ok (value, reader)
  | .fail error, _ => .error error
  | .bits count eofError next, reader =>
    match reader.readBits count with
    | none => .error eofError
    | some (value, rest) => eval (next value) rest
  | .align next, reader => eval next reader.alignToByte

end Parser

inductive RunResult (α : Type) where
  | done (value : α) (state : Reservoir)
  | error (error : Deflate.DecompressError) (state : Reservoir)
  | needInput (continuation : Parser α) (state : Reservoir)
  | yield (continuation : Parser α) (state : Reservoir)

def RunResult.state {α : Type} : RunResult α → Reservoir
  | .done _ state | .error _ state | .needInput _ state | .yield _ state => state

/-- The observation of a result from an appropriately related logical reader.
Suspended and yielded results continue from their retained parsing program. -/
def RunResult.observe {α : Type} : RunResult α → LSBReader →
    Except Deflate.DecompressError (α × LSBReader)
  | .done value _, reader => .ok (value, reader)
  | .error err _, _ => .error err
  | .needInput continuation _, reader | .yield continuation _, reader => continuation.eval reader

namespace Parser

def run {α : Type} : Nat → Parser α → Reservoir → RunResult α
  | 0, parser, state => .yield parser state
  | fuel + 1, parser, state =>
    match parser with
    | .pure value => .done value state
    | .fail error => .error error state
    | .bits count error next =>
      match Reservoir.readBits count state with
      | .value value rest => run fuel (next value) rest
      | .needInput filled => .needInput (.bits count error next) filled
    | .align next => run fuel next state.byteBits

end Parser
end Silmaril.Formats.Compression.Inflate.Stream
