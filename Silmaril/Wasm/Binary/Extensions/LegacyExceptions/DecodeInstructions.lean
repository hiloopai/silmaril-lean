module

public import Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Instructions
public import Silmaril.Wasm.Binary.Extensions.BinaryenMemory.DecodeInstructions
public import Silmaril.Wasm.Binary.Extensions.Structured.DecodeDelimited

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode

open Core Core.Decode

/-- `term` was consumed by the preceding body reader. Catch-all is final, and
legacy delegate is handled only by the outer try production. -/
def readHandlers (reader : Nat → DecodeM Wasm.Extensions.LegacyExceptions.Leaf) :
    Nat → UInt8 → DecodeM ((List (TagIdx × Wasm.Extensions.LegacyExceptions.Expr)) × Option Wasm.Extensions.LegacyExceptions.Expr)
  | 0, _ => decodeError "out of fuel"
  | fuel + 1, term =>
    if term == 0x0b then pure ([], none)
    else if term == 0x07 then do
      let tag ← readIdx
      let (body, next) ← Structured.Decode.readSeqUntil reader [0x07, 0x19, 0x0b] fuel
      let (catches, all) ← readHandlers reader fuel next
      pure ((tag, body) :: catches, all)
    else if term == 0x19 then do
      let (body, _) ← Structured.Decode.readSeqUntil reader [0x0b] fuel
      pure ([], some body)
    else decodeError "unexpected legacy exception handler delimiter"

def readLeaf : Nat → Nat → DecodeM Wasm.Extensions.LegacyExceptions.Leaf
  | 0, _ => decodeError "out of fuel"
  | fuel + 1, op =>
    if op == 0x06 then do
      let type ← readBlockType
      let (body, term) ← Structured.Decode.readSeqUntil (readLeaf fuel) [0x07, 0x19, 0x18, 0x0b] fuel
      if term == 0x18 then
        let label ← readIdx
        pure (.delegate type body label)
      else
        let (catches, all) ← readHandlers (readLeaf fuel) fuel term
        pure (.try_ type body catches all)
    else if op == 0x09 then do
      pure (.rethrow (← readIdx))
    else
      (BinaryenMemory.Decode.readLeaf op).map Wasm.Extensions.LegacyExceptions.Leaf.base

def readExpr : DecodeM Wasm.Extensions.LegacyExceptions.Expr := do
  let n ← remaining
  Structured.Decode.readExpr (readLeaf (n + 1))

end Silmaril.Wasm.Binary.Extensions.LegacyExceptions.Decode
