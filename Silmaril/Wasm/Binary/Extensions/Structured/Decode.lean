module

public import Silmaril.Wasm.Binary.Extensions.Structured.Instructions
public import Silmaril.Wasm.Binary.Core.Decode

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.Structured.Decode

open Core Core.Decode

mutual
/-- One instruction whose opcode `op` has been read. Structural on `fuel`. -/
def readInstr {Leaf : Type} (reader : Nat → DecodeM Leaf) (fuel : Nat) (op : Nat) : DecodeM (Wasm.Extensions.Structured.Instr Leaf) :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 =>
    match op with
    | 0x02 => do
      let bt ← readBlockType
      let (body, t) ← readSeq reader fuel
      if t == 0x0B then pure (.block bt body) else decodeError "`else` inside `block`"
    | 0x03 => do
      let bt ← readBlockType
      let (body, t) ← readSeq reader fuel
      if t == 0x0B then pure (.loop bt body) else decodeError "`else` inside `loop`"
    | 0x04 => do
      let bt ← readBlockType
      let (thn, t) ← readSeq reader fuel
      if t == 0x0B then pure (.if_ bt thn [])
      else
        let (els, t') ← readSeq reader fuel
        if t' == 0x0B then pure (.if_ bt thn els) else decodeError "second `else` in `if`"
    | 0x1F => do
      let bt ← readBlockType
      let cs ← readVec readCatch
      let (body, t) ← readSeq reader fuel
      if t == 0x0B then pure (.tryTable bt cs body) else decodeError "`else` inside `try_table`"
    | op => do pure (.leaf (← reader op))
/-- Instructions up to and including a terminator (`end` 0x0B or `else` 0x05), which
is returned. Structural on `fuel`. -/
def readSeq {Leaf : Type} (reader : Nat → DecodeM Leaf) (fuel : Nat) : DecodeM (List (Wasm.Extensions.Structured.Instr Leaf) × UInt8) :=
  match fuel with
  | 0 => decodeError "out of fuel"
  | fuel + 1 => do
    let b ← readByte
    if b == 0x0B || b == 0x05 then pure ([], b)
    else
      let i ← readInstr reader fuel b.toNat
      let (rest, t) ← readSeq reader fuel
      pure (i :: rest, t)
end

/-- An expression: instructions, then `end`. -/
def readExpr {Leaf : Type} (reader : Nat → DecodeM Leaf) : DecodeM (Wasm.Extensions.Structured.Expr Leaf) := do
  let (is, t) ← readSeq reader ((← remaining) + 1)
  if t == 0x0B then pure is else decodeError "`else` outside `if`"


end Silmaril.Wasm.Binary.Extensions.Structured.Decode
