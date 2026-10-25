module

public import Silmaril.Wasm.Execution.Runtime
public import Silmaril.Wasm.Execution.Memory
public import Silmaril.Wasm.Numerics.Float
public import Silmaril.Wasm.V1.ToCore.Types

/-! # Runtime operations for WebAssembly 1.0 -/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

abbrev Admin := AdminInstr Instr
abbrev Store (Host : Type*) := Runtime.Store Func Host
abbrev Config (Host : Type*) := Runtime.Config Func Host Instr
abbrev HostSemantics (Host : Type*) := Runtime.HostSemantics Func Host

/-- Runtime values are already source constants, rather than a second literal syntax. -/
def value : Value → Admin
  | ⟨.int t, bits⟩ => .source (.intConst t bits)
  | ⟨.float t, bits⟩ => .source (.floatConst t bits)

def values (vs : List Value) : List Admin := vs.map value
def expression (es : Expr) : List Admin := es.map .source

def result : Result → List Admin
  | .values vs => values vs
  | .trap => [.trap]

def lowerLabel (i : LabelIdx) : LabelIdx :=
  ⟨⟨i.toNat - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.value.isLt⟩⟩

def frameMemory {H : Type*} (s : Store H) (f : Frame) : Option (MemAddr × MemInst) := do
  let a ← f.module.memories[0]?
  let m ← s.memories[a.value]?
  return (a, m)

def frameTable {H : Type*} (s : Store H) (f : Frame) : Option TableInst := do
  let a ← f.module.tables[0]?
  s.tables[a.value]?

/-- Effective addresses are natural sums; overflow is not wrapped away. -/
def effectiveAddress (address : BitVec 32) (arg : MemArg) : Nat := address.toNat + arg.offset.val

def loadInt (t : IntType) (packed : Option (PackSize × Signedness))
    (memory : Memory.Bytes) (start : Nat) : Option Value :=
  match packed with
  | none => (Memory.load memory start (t.width / 8)).map fun x =>
      .int t (x.setWidth t.width)
  | some (p, sign) => (Memory.load memory start (p.width / 8)).map fun x =>
      .int t (match sign with
        | .unsigned => x.setWidth t.width
        | .signed => x.signExtend t.width)

def loadFloat (t : FloatType) (memory : Memory.Bytes) (start : Nat) : Option Value :=
  (Memory.load memory start (t.width / 8)).map fun x => .float t (x.setWidth t.width)

def storeInt (t : IntType) (packed : Option PackSize) (memory : Memory.Bytes) (start : Nat)
    (x : BitVec t.width) : Option Memory.Bytes :=
  let width := (packed.map PackSize.width).getD t.width
  Memory.store memory start (count := width / 8) (x.setWidth (8 * (width / 8)))

def storeFloat (t : FloatType) (memory : Memory.Bytes) (start : Nat) (x : BitVec t.width) :
    Option Memory.Bytes :=
  Memory.store memory start (count := t.width / 8) (x.setWidth (8 * (t.width / 8)))

def setMemory {H : Type*} (s : Store H) (a : MemAddr) (m : MemInst) : Store H :=
  { s with memories := s.memories.set a.value m }

def setGlobal {H : Type*} (s : Store H) (a : GlobalAddr) (g : GlobalInst) : Store H :=
  { s with globals := s.globals.set a.value g }

@[simp] theorem values_append (xs ys : List Value) : values (xs ++ ys) = values xs ++ values ys :=
  List.map_append

@[simp] theorem values_length (xs : List Value) : (values xs).length = xs.length :=
  List.length_map value

@[simp] theorem expression_append (xs ys : Expr) :
    expression (xs ++ ys) = expression xs ++ expression ys := List.map_append

end Silmaril.Wasm.V1.Execution
