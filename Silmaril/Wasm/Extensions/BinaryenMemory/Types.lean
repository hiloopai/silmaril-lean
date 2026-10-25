module

public import Silmaril.Wasm.Extensions.AtomicMemory.Types

/-! # Explicit Binaryen memory proposal syntax

Array backing and atomic memory order are retained data, never large alignments
or ordinary memory indices. This is syntax support, without an operational
semantics or validity claim for the experimental proposals.
-/

@[expose] public section

namespace Silmaril.Wasm.Extensions.BinaryenMemory

/-- The contiguous scalar memory opcode table, 0x28 through 0x3e. -/
structure ScalarOp where
  code : Fin 23
  deriving DecidableEq, Repr

def ScalarOp.opcode (op : ScalarOp) : UInt8 := (0x28 + op.code.val).toUInt8

inductive MemoryOrder where
  | seqcst | acqrel | relaxed
  deriving DecidableEq, Repr

def MemoryOrder.code : MemoryOrder → UInt8
  | .seqcst => 0 | .acqrel => 1 | .relaxed => 2

def MemoryOrder.rmwCode (o : MemoryOrder) : UInt8 := 17 * o.code

def MemoryOrder.ofCode? : UInt8 → Option MemoryOrder
  | 0 => some .seqcst | 1 => some .acqrel | 2 => some .relaxed | _ => none

def MemoryOrder.ofRMWCode? : UInt8 → Option MemoryOrder
  | 0 => some .seqcst | 17 => some .acqrel | 34 => some .relaxed | _ => none

def isRMW : AtomicMemory.Access → Bool
  | .rmw _ _ | .cmpxchg _ => true
  | _ => false

def orderable : AtomicMemory.Access → Bool
  | .load _ | .store _ | .rmw _ _ | .cmpxchg _ => true
  | _ => false

def MemoryOrder.accessCode (o : MemoryOrder) (op : AtomicMemory.Access) : UInt8 :=
  if isRMW op then o.rmwCode else o.code

inductive Leaf where
  | base (i : AtomicMemory.Leaf)
  | arrayAccess (op : ScalarOp) (type : TypeIdx) (arg : MemArg)
  | vectorArrayAccess (store : Bool) (type : TypeIdx) (arg : MemArg)
  | orderedAccess (op : AtomicMemory.Access) (memory : MemIdx) (arg : MemArg) (order : MemoryOrder)
  | orderedFence (order : MemoryOrder)
  deriving Repr

def Leaf.contextShape : Leaf → Wasm.Instr
  | .base i => i.contextShape
  | _ => .nop

abbrev Instr := Structured.Instr Leaf
abbrev Expr := Structured.Expr Leaf
abbrev Func := Declaration.Func ValType Expr
abbrev Module := Structured.FunctionModule Expr

def contextShape (m : Module) : SharedMemory.Module :=
  m.contextShape (Structured.Expr.contextShape Leaf.contextShape)

end Silmaril.Wasm.Extensions.BinaryenMemory
