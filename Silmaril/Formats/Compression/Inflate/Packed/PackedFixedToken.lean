module

public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedDecode

/-!
# Buffered fixed-table tokens

Two independent packed operations compose into the
existing token parser. Thirty-one already-buffered bits suffice for every
fixed literal, end marker, length/distance pair, or reserved-code rejection.
The trace retains each code and extra-bit count, and the complete physical
result is one exact drop of their sum: no input is pulled.

The reserved distance symbol is recovered from the fixed root witness solely
to retain the mathematical parser's precise error. Packed C operations do not
retain that symbol. This is a mathematical parsing refinement, not execution
of C/Core/machine code, refill, or output/history validation.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Manual.PackedTables

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Inflate.Stream

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

structure TokenTrace where
  literalCode : Nat
  literalExtra : Nat
  distanceCode : Nat
  distanceExtra : Nat
  deriving Repr, DecidableEq

def TokenTrace.total (trace : TokenTrace) : Nat :=
  trace.literalCode + trace.literalExtra + trace.distanceCode + trace.distanceExtra

inductive TokenResult where
  | value (token : Token) (after : Reservoir) (trace : TokenTrace)
  | error (error : Deflate.DecompressError) (after : Reservoir) (trace : TokenTrace)
  | incomplete
  deriving Repr

/-- A bounded mathematical adapter around the two packed operations. The
incomplete result is unreachable under the theorem's buffered-bit premise;
this adapter does not specify resumption when that premise is unavailable. -/
def decodeFixedToken (state : Reservoir) : TokenResult :=
  match decode .literalLength lenfix 9 state with
  | .value (.literal value) rest code extra =>
    .value (.literal (UInt8.ofNat value)) rest ⟨code, extra, 0, 0⟩
  | .value .endBlock rest code extra => .value .endBlock rest ⟨code, extra, 0, 0⟩
  | .value (.amount length) rest code extra =>
    match decode .distance distfix 5 rest with
    | .value (.amount distance) after distanceCode distanceExtra =>
      .value (.matchBytes length distance) after ⟨code, extra, distanceCode, distanceExtra⟩
    | .invalid after distanceCode =>
      .error (.badDistanceCode (distanceRootCode (rest.lowBits 5)).symbol) after
        ⟨code, extra, distanceCode, 0⟩
    | _ => .incomplete
  | .invalid after code => .error .decodeOverrun after ⟨code, 0, 0, 0⟩
  | _ => .incomplete

def TokenCorrespondence (before : Reservoir) (reader : LSBReader) : TokenResult → Prop
  | .value token after trace =>
    ∃ canonical, parseToken fixedLiteralTable fixedDistanceTable reader = .ok (token, canonical) ∧
      Reservoir.Normalizes after canonical ∧ after = before.dropBits trace.total ∧ trace.total ≤ 31
  | .error error after trace =>
    parseToken fixedLiteralTable fixedDistanceTable reader = .error error ∧
      after = before.dropBits trace.total ∧ after.Valid ∧ trace.total ≤ 31
  | .incomplete => False

/-- Distance parsing after the length and its extra bits have been consumed. -/
def parseDistance (table : HuffmanTable) (length : Nat) (reader : LSBReader) :
    Except Deflate.DecompressError (Token × LSBReader) :=
  match table.readSymbolLSB reader with
  | none => .error .decodeOverrun
  | some (symbol, rest) =>
    if 30 ≤ symbol then .error (.badDistanceCode symbol)
    else
      match rest.readBits (Deflate.distanceExtraBits.getD symbol 0) with
      | none => .error .decodeOverrun
      | some (extra, after) =>
        .ok (.matchBytes length (Deflate.distanceBase.getD symbol 1 + extra), after)

/-- A cost predicate independent of whether a buffered operation succeeds.
The complete correspondence separately rules out suspended cases. -/
def DecodeBudget (limit : Nat) : DecodeResult → Prop
  | .value _ _ code extra => code + extra ≤ limit
  | .invalid _ code => code ≤ limit
  | _ => True

end Silmaril.Formats.Compression.Inflate.Manual.PackedTables
