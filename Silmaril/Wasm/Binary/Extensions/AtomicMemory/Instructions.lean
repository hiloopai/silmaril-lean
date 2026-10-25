module

public import Silmaril.Wasm.Extensions.AtomicMemory.Types
public import Silmaril.Wasm.Binary.Extensions.Structured.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.AtomicMemory

open Core

inductive Atomic (F : Forms) : Bytes → Wasm.Extensions.AtomicMemory.AtomicInstr → Prop where
  | access {bn bm : Bytes} {op : Wasm.Extensions.AtomicMemory.Access} {m : MemIdx} {a : MemArg}
      (hn : U32 bn op.opcode) (hm : Core.Memarg F bm (m, a)) :
      Atomic F ([0xfe] ++ bn ++ bm) (.access op m a)
  | fence {bn : Bytes} (hn : U32 bn 3) : Atomic F ([0xfe] ++ bn ++ [0]) .fence
  | pause {bn : Bytes} (hn : U32 bn 4) : Atomic F ([0xfe] ++ bn) .pause

/-- The Core branch excludes structured opcodes and the owned atomic prefix.
Extensions cannot hide in a Core instruction certificate. -/
inductive Leaf (F : Forms) : Bytes → Wasm.Extensions.AtomicMemory.Leaf → Prop where
  | core {op : UInt8} {b : Bytes} {i : Wasm.Instr}
      (hop : op.toNat ∉ [0x02, 0x03, 0x04, 0x1f, 0xfe])
      (h : Core.Instr F ([op] ++ b) i) : Leaf F ([op] ++ b) (.core i)
  | atomic {b : Bytes} {i : Wasm.Extensions.AtomicMemory.AtomicInstr}
      (h : Atomic F b i) : Leaf F b (.atomic i)

abbrev Instr (F : Forms) := Structured.Instr F (Leaf F)
abbrev Instrs (F : Forms) := Structured.Instrs F (Leaf F)
abbrev Expr (F : Forms) := Structured.Expr F (Leaf F)

end Silmaril.Wasm.Binary.Extensions.AtomicMemory
