module

public import Silmaril.Wasm.Extensions.StructuredInstructions

/-! # Explicit memory-atomic instruction syntax

The seven integer memory shapes and six arithmetic/exchange RMW families cover
the original threads proposal's complete linear-memory instruction table.
GC/reference atomics and memory-order proposals are separate extensions.
No concurrent operational semantics is asserted by these syntax definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Extensions.AtomicMemory

inductive Shape where
  | i32 | i64 | i32_8 | i32_16 | i64_8 | i64_16 | i64_32
  deriving DecidableEq, Repr

def Shape.code : Shape → Nat
  | .i32 => 0 | .i64 => 1 | .i32_8 => 2 | .i32_16 => 3
  | .i64_8 => 4 | .i64_16 => 5 | .i64_32 => 6

def Shape.all : List Shape := [.i32, .i64, .i32_8, .i32_16, .i64_8, .i64_16, .i64_32]

inductive RMW where
  | add | sub | and | or | xor | xchg
  deriving DecidableEq, Repr

def RMW.code : RMW → Nat
  | .add => 0 | .sub => 1 | .and => 2 | .or => 3 | .xor => 4 | .xchg => 5

def RMW.all : List RMW := [.add, .sub, .and, .or, .xor, .xchg]

inductive Access where
  | notify | wait32 | wait64
  | load (shape : Shape)
  | store (shape : Shape)
  | rmw (op : RMW) (shape : Shape)
  | cmpxchg (shape : Shape)
  deriving DecidableEq, Repr

def Access.opcode : Access → Nat
  | .notify => 0 | .wait32 => 1 | .wait64 => 2
  | .load s => 0x10 + s.code
  | .store s => 0x17 + s.code
  | .rmw op s => 0x1e + 7 * op.code + s.code
  | .cmpxchg s => 0x48 + s.code

def Access.all : List Access :=
  [.notify, .wait32, .wait64] ++ Shape.all.map .load ++ Shape.all.map .store ++
    (RMW.all.flatMap fun op => Shape.all.map (Access.rmw op)) ++ Shape.all.map .cmpxchg

def Access.ofOpcode? (n : Nat) : Option Access := Access.all.find? (fun op => op.opcode == n)

inductive AtomicInstr where
  | access (op : Access) (memory : MemIdx) (arg : MemArg)
  | fence
  | pause
  deriving DecidableEq, Repr

inductive Leaf where
  | core (i : Wasm.Instr)
  | atomic (i : AtomicInstr)
  deriving Repr

def Leaf.contextShape : Leaf → Wasm.Instr
  | .core i => i
  | .atomic _ => .nop

abbrev Instr := Structured.Instr Leaf
abbrev Expr := Structured.Expr Leaf
abbrev Func := Declaration.Func ValType Expr
abbrev Module := Structured.FunctionModule Expr

def contextShape (m : Module) : SharedMemory.Module :=
  m.contextShape (Structured.Expr.contextShape Leaf.contextShape)

end Silmaril.Wasm.Extensions.AtomicMemory
