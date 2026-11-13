module

public import Silmaril.Compiler.Native.Emit.Prologue.Defs
public import Silmaril.Machine.CBackend.Lir.Semantics.Defs
public import Silmaril.X86.Ext.Store
/-! A small actual native scalar selector for slots 2 through 10. Instruction
execution and stack representation are separate from GNU-as text encoding. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Scalar
open Silmaril Silmaril.X86

/-- The nine scalar slots used by the actual unoptimized addition body. -/
abbrev Register := Fin 9

def Register.index (register : Register) : Nat := register.val + 2

def address (stack : Word) (register : Register) : Word :=
  stack - BitVec.ofNat 64 (8 * (register.index + 2))

def footprint (stack : Word) (location : Nat) : Prop :=
  stack.toNat - 96 ≤ location ∧ location < stack.toNat - 24

inductive Operation where
  | constant (destination : Register) (value : Word)
  | sext32 (destination source : Register)
  | add (destination left right : Register)

def Operation.destination : Operation → Register
  | .constant destination _ | .sext32 destination _ | .add destination _ _ => destination

def Operation.lir : Operation → Silmaril.Machine.Lir.Op Nat
  | .constant destination value => .const destination.index value
  | .sext32 destination source => .unary .sext32 destination.index source.index
  | .add destination left right => .binary .add destination.index left.index right.index

def Operation.instructions : Operation → List Ext.Instr
  | .constant destination value =>
      [.movabs .rax value, .mov .q (.mem (Prologue.slot destination.index)) .rax]
  | .sext32 destination source =>
      [.load .q .rax (Prologue.slot source.index), .movsxd .rax (.reg .rax),
        .mov .q (.mem (Prologue.slot destination.index)) .rax]
  | .add destination left right =>
      [.load .q .rax (Prologue.slot left.index), .load .q .r10 (Prologue.slot right.index),
        .alu .q .add (.reg .rax) .r10, .mov .q (.mem (Prologue.slot destination.index)) .rax]

def Operation.render : Operation → String
  | .constant destination value => s!"  movabs rax, {value.toNat}\n" ++ Asm.write destination.index
  | .sext32 destination source => Asm.read source.index ++ Asm.unary .sext32 ++ Asm.write destination.index
  | .add destination left right =>
      Asm.read left.index ++ Asm.read right.index "r10" ++ Asm.binary .add ++ Asm.write destination.index

def Operation.value (frame : Silmaril.Machine.Lir.Frame Nat) : Operation → Option Word
  | .constant _ value => some value
  | .sext32 _ source => frame.get source.index |>.map Silmaril.Machine.Lir.Unop.sext32.eval
  | .add _ left right => do
      let left ← frame.get left.index
      let right ← frame.get right.index
      return left + right

def Operation.bytes : Operation → Nat
  | .constant .. => 14
  | .sext32 .. => 11
  | .add .. => 15

def evaluate : List Operation → Silmaril.Machine.Lir.Frame Nat → Option (Silmaril.Machine.Lir.Frame Nat)
  | [], frame => some frame
  | operation :: rest, frame => do
      let value ← operation.value frame
      evaluate rest (frame.set operation.destination.index value)

/-- Only written virtual registers require physical backing. -/
def Represents (stack : Word) (memory : Process.Memory) (frame : Silmaril.Machine.Lir.Frame Nat) : Prop :=
  ∀ register : Register, ∀ value, frame.get register.index = some value →
    Ext.HoldsLE memory (address stack register).toNat 8 value

structure Entry (stack : Word) (before : X86.MState) : Prop where
  lower : 96 ≤ stack.toNat
  base : before.core.read .rbp = stack - 8
  readable : before.memory.Permitted .read (stack.toNat - 96) 72
  writable : before.memory.Permitted .write (stack.toNat - 96) 72

/-- RAX/R10 and arithmetic flags are scratch. Every other GP register and FS
base are preserved, and writes stay inside the nine physical scalar slots. -/
structure Result (stack : Word) (before after : X86.MState) (frame : Silmaril.Machine.Lir.Frame Nat)
    (bytes : Nat) : Prop where
  pc : after.core.rip = before.core.rip + BitVec.ofNat 64 bytes
  registers : ∀ register, register ≠ .rax → register ≠ .r10 → after.core.read register = before.core.read register
  fsBase : after.core.fsBase = before.core.fsBase
  memory : before.memory.WritesWithin after.memory (footprint stack)
  represented : Represents stack after.memory frame

end Silmaril.Compiler.Native.Emit.Scalar
