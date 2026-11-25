module

public import Silmaril.Machine.DecodeGraph.Defs
public import Silmaril.Machine.Decoder

/-! # Adapter for the existing bit-vector-list machine codec -/

@[expose] public section

namespace Silmaril.Machine.DecodeGraph

open Silmaril.Parse.DecodeGraph

variable {Context Source : Type*}

/-- This is the only representation boundary to `Machine.Decoder`. -/
def decoderWindow (bytes : List UInt8) (pos stop : Nat) : List (BitVec 8) :=
  (bytes.extract pos stop).map UInt8.toBitVec

/-- Lift a context-free machine codec to reference cursor queries. The codec
chooses a width; the graph reports an end cursor. -/
def ofDecoder (decoder : Decoder Source) : Reference Context Source :=
  Set.ofPred fun (input, result) =>
    input.stop ≤ input.bytes.length ∧
      ∃ width, decoder.decode (decoderWindow input.bytes input.pos input.stop) = some (result.1, width) ∧
        result.2 = input.pos + width

/-- Scan a candidate prefix with the unchanged sequential decoder. Its listing
offsets are erased and it does not require a terminator. -/
def sequentialPrefixes (decoder : Decoder Source) (fuel : Nat) : Reference Context (List Source) :=
  Set.ofPred fun (input, result) =>
    input.pos ≤ result.2 ∧ result.2 ≤ input.stop ∧ input.stop ≤ input.bytes.length ∧
    (decoder.decodeBlock fuel input.pos (decoderWindow input.bytes input.pos result.2)).map (List.map Prod.snd) =
      some result.1

end Silmaril.Machine.DecodeGraph
