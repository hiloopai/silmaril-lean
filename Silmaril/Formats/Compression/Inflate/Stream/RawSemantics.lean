module

public import Silmaril.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation
public import Silmaril.Formats.Compression.Inflate.Stream.Progress
public import Silmaril.Formats.Compression.Inflate.Stream.Blocks

/-!
# Continuation semantics of the whole raw inflater

The controller has no semantic fuel or declared input length. Its meaning is
the existing mathematical decoder applied to its current mode and unread bits.
Only caller scheduling is bounded. Completed raw streams discard their final
partial-byte padding while retaining complete prefetched bytes.

This is the logical parsing/output controller, not execution of zlib's packed
tables, physical C window, fast path, wrapper or public status protocol.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.RawSemantics

open Silmaril.Formats.Compression

abbrev Result := Except Deflate.DecompressError (List UInt8 × LSBReader)

def alignResult (result : Result) : Result :=
  result.map fun pair => (pair.1, pair.2.alignToByte)

/-- Decode all remaining blocks. The specification's fuel is a local proof
device, not a field or a limit in the executable controller. -/
def format (reader : LSBReader) (output : List UInt8) : Result :=
  alignResult (Deflate.decompressBlocks (reader.bitsLeft + 1) reader output)

def afterBlock (last : Bool) (output : List UInt8) (reader : LSBReader) : Result :=
  if last then .ok (output, reader.alignToByte) else format reader output

def afterDecodedBlock (last : Bool) (result : Result) : Result :=
  match result with
  | .error err => .error err
  | .ok (output, reader) => afterBlock last output reader

def afterToken (last : Bool) (litLen dist : HuffmanTable)
    (result : Except Deflate.DecompressError Deflate.SymbolStep) : Result :=
  match result with
  | .error err => .error err
  | .ok (.done output reader) => afterBlock last output reader
  | .ok (.more output reader) =>
    afterDecodedBlock last (Deflate.decodeSymbol litLen dist reader output)

def denote : RawMachine → LSBReader → Result
  | .header parser state, reader =>
    match parser.eval reader with
    | .error err => .error err
    | .ok ((last, kind), rest) =>
      afterDecodedBlock last (Deflate.decompressBlockBody kind rest state.output)
  | .storedHeader last parser state, reader =>
    match parser.eval reader with
    | .error err => .error err
    | .ok (remaining, rest) =>
      afterDecodedBlock last (Deflate.readStoredBytes state.output rest remaining)
  | .storedCopy last remaining state, reader =>
    afterDecodedBlock last (Deflate.readStoredBytes state.output reader remaining)
  | .dynamicTables last parser state, reader =>
    match parser.eval reader with
    | .error err => .error err
    | .ok ((litLen, dist), rest) =>
      afterDecodedBlock last (Deflate.decodeSymbol litLen dist rest state.output)
  | .symbols last litLen dist machine, reader =>
    afterToken last litLen dist (TokenContinuation.denote machine reader)
  | .done state, reader => .ok (state.output, reader)
  | .bad err _, _ => .error err

/-- History remains represented in every raw phase. Parsing-token continuations
also retain their range and completion invariants across future input. -/
def WellFormed (machine : RawMachine) (reader : LSBReader) : Prop :=
  machine.window.Represents machine.output ∧
    match machine with
    | .symbols _ _ _ token => TokenContinuation.WellFormed token reader
    | _ => True

end Silmaril.Formats.Compression.Inflate.Stream.RawSemantics
