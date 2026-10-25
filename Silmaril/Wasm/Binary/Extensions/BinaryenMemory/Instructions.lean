module

public import Silmaril.Wasm.Extensions.BinaryenMemory.Types
public import Silmaril.Wasm.Binary.Extensions.AtomicMemory.Instructions

@[expose] public section

namespace Silmaril.Wasm.Binary.Extensions.BinaryenMemory

open Core Wasm.Extensions.BinaryenMemory

/-- Bit 5 selects array backing; the ordinary alignment is retained separately.
The trailing type index belongs to the access, not a following instruction. -/
inductive ArrayAccess : Bytes → Wasm.Extensions.BinaryenMemory.Leaf → Prop where
  | mk {bn bo bt : Bytes} {op : ScalarOp} {type : TypeIdx} {arg : MemArg}
      (ha : arg.align.val < 16) (hn : U32 bn (32 + arg.align.val))
      (ho : U32 bo arg.offset.val) (ht : Index bt type) :
      ArrayAccess ([op.opcode] ++ bn ++ bo ++ bt) (.arrayAccess op type arg)

/-- Binaryen also permits the full-width v128 load/store on array backing. -/
inductive VectorArrayAccess : Bytes → Wasm.Extensions.BinaryenMemory.Leaf → Prop where
  | mk {bc bn bo bt : Bytes} {store : Bool} {type : TypeIdx} {arg : MemArg}
      (hc : U32 bc (if store then 11 else 0))
      (ha : arg.align.val < 16) (hn : U32 bn (32 + arg.align.val))
      (ho : U32 bo arg.offset.val) (ht : Index bt type) :
      VectorArrayAccess ([0xfd] ++ bc ++ bn ++ bo ++ bt) (.vectorArrayAccess store type arg)

/-- Bit 4 selects an explicit atomic memory order; bit 6 selects a memory index.
RMW operations require the duplicated matching order code. -/
inductive OrderedMemarg (op : Wasm.Extensions.AtomicMemory.Access) :
    Bytes → MemIdx × MemArg × MemoryOrder → Prop where
  | zero {bn bo : Bytes} {arg : MemArg} {order : MemoryOrder}
      (ha : arg.align.val < 16) (hn : U32 bn (16 + arg.align.val))
      (ho : U64 bo arg.offset.val) :
      OrderedMemarg op (bn ++ [order.accessCode op] ++ bo) (⟨0⟩, arg, order)
  | indexed {bn bm bo : Bytes} {memory : MemIdx} {arg : MemArg} {order : MemoryOrder}
      (ha : arg.align.val < 16) (hn : U32 bn (80 + arg.align.val))
      (hm : Index bm memory) (ho : U64 bo arg.offset.val) :
      OrderedMemarg op (bn ++ bm ++ [order.accessCode op] ++ bo) (memory, arg, order)

inductive OrderedAtomic : Bytes → Wasm.Extensions.BinaryenMemory.Leaf → Prop where
  | access {bn bm : Bytes} {op : Wasm.Extensions.AtomicMemory.Access} {memory : MemIdx}
      {arg : MemArg} {order : MemoryOrder} (horder : orderable op = true)
      (hn : U32 bn op.opcode) (hm : OrderedMemarg op bm (memory, arg, order)) :
      OrderedAtomic ([0xfe] ++ bn ++ bm) (.orderedAccess op memory arg order)
  | fence {bn : Bytes} {order : MemoryOrder} (hn : U32 bn 3) :
      OrderedAtomic ([0xfe] ++ bn ++ [order.code]) (.orderedFence order)

inductive Leaf (F : Forms) : Bytes → Wasm.Extensions.BinaryenMemory.Leaf → Prop where
  | base {b : Bytes} {i : Wasm.Extensions.AtomicMemory.Leaf} (h : AtomicMemory.Leaf F b i) :
      Leaf F b (.base i)
  | array {b : Bytes} {i : Wasm.Extensions.BinaryenMemory.Leaf} (h : ArrayAccess b i) : Leaf F b i
  | vectorArray {b : Bytes} {i : Wasm.Extensions.BinaryenMemory.Leaf} (h : VectorArrayAccess b i) : Leaf F b i
  | ordered {b : Bytes} {i : Wasm.Extensions.BinaryenMemory.Leaf} (h : OrderedAtomic b i) : Leaf F b i

abbrev Instr (F : Forms) := Structured.Instr F (Leaf F)
abbrev Instrs (F : Forms) := Structured.Instrs F (Leaf F)
abbrev Expr (F : Forms) := Structured.Expr F (Leaf F)

end Silmaril.Wasm.Binary.Extensions.BinaryenMemory
