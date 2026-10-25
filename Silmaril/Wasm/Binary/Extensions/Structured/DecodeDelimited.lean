module

public import Silmaril.Wasm.Binary.Extensions.Structured.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.Decode

open Core Core.Decode

/-- Reusable expression sequence with a caller-specified delimiter alphabet.
Nested block/loop/if/try_table instructions keep their own normal delimiters. -/
def readSeqUntil {Leaf : Type} (reader : Nat → DecodeM Leaf) (stops : List UInt8) :
    Nat → DecodeM (List (Wasm.Extensions.Structured.Instr Leaf) × UInt8)
  | 0 => decodeError "out of fuel"
  | fuel + 1 => do
    let b ← readByte
    if b ∈ stops then pure ([], b)
    else
      let i ← readInstr reader fuel b.toNat
      let (rest, term) ← readSeqUntil reader stops fuel
      pure (i :: rest, term)

end Silmaril.Wasm.Binary.Extensions.Structured.Decode
