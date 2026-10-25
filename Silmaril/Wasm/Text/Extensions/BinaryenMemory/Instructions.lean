module

public import Silmaril.Wasm.Extensions.BinaryenMemory.Types
public import Silmaril.Wasm.Text.Extensions.AtomicMemory.Instructions

@[expose] public section

namespace Silmaril.Wasm.Extensions.BinaryenMemory

def scalarNames : List String :=
  ["i32.load", "i64.load", "f32.load", "f64.load", "i32.load8_s", "i32.load8_u",
   "i32.load16_s", "i32.load16_u", "i64.load8_s", "i64.load8_u", "i64.load16_s", "i64.load16_u",
   "i64.load32_s", "i64.load32_u", "i32.store", "i64.store", "f32.store", "f64.store",
   "i32.store8", "i32.store16", "i64.store8", "i64.store16", "i64.store32"]

def scalarWidths : List Nat := [4, 8, 4, 8, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 4, 8, 4, 8, 1, 2, 1, 2, 4]

def ScalarOp.mnemonic (op : ScalarOp) : String :=
  scalarNames[op.code.val]'(by simp [scalarNames])

def ScalarOp.width (op : ScalarOp) : Nat :=
  scalarWidths[op.code.val]'(by simp [scalarWidths])

def MemoryOrder.name : MemoryOrder → String
  | .seqcst => "seqcst" | .acqrel => "acqrel" | .relaxed => "relaxed"

end Silmaril.Wasm.Extensions.BinaryenMemory

namespace Silmaril.Wasm.Text.Extensions.BinaryenMemory

open Silmaril Silmaril.Formats.SExpEncoding Wasm.Extensions.BinaryenMemory

inductive LeafT (I : Core.IdCtx) : List SExp → Wasm.Extensions.BinaryenMemory.Leaf → Prop where
  | base {xs : List SExp} {i : Wasm.Extensions.AtomicMemory.Leaf} (h : AtomicMemory.LeafT I xs i) :
      LeafT I xs (.base i)
  | array {xs : List SExp} {ix : SExp} {op : ScalarOp} {type : TypeIdx} {arg : MemArg}
      (hi : Text.Idx I.types ix type) (ha : Core.MemArgT op.width xs arg) :
      LeafT I (K op.mnemonic :: L [K "type", ix] :: xs) (.arrayAccess op type arg)
  | vectorArray {xs : List SExp} {ix : SExp} {store : Bool} {type : TypeIdx} {arg : MemArg}
      (hi : Text.Idx I.types ix type) (ha : Core.MemArgT 16 xs arg) :
      LeafT I (K (if store then "v128.store" else "v128.load") :: L [K "type", ix] :: xs)
        (.vectorArrayAccess store type arg)
  | ordered {xs : List SExp} {ix : SExp} {op : Wasm.Extensions.AtomicMemory.Access}
      {memory : MemIdx} {arg : MemArg} {order : MemoryOrder} (horder : orderable op = true)
      (hi : Text.Idx I.mems ix memory) (ha : Core.MemArgT op.width xs arg) :
      LeafT I (K op.mnemonic :: ix :: K order.name :: xs) (.orderedAccess op memory arg order)
  | fence {order : MemoryOrder} : LeafT I [K "atomic.fence", K order.name] (.orderedFence order)

abbrev InstrT := Structured.InstrT LeafT
abbrev InstrsT := Structured.InstrsT LeafT

end Silmaril.Wasm.Text.Extensions.BinaryenMemory
