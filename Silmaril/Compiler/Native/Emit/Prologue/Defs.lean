module

public import Silmaril.Compiler.Native.Asm.Defs
public import Silmaril.X86.Ext.Semantics
/-! Shared native frame-prologue selection. Its renderer replaces the exact
existing Emit prefix; its instruction interpretation uses actual Ext.exec.
GNU-as correspondence and a whole native function refinement are separate. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Emit.Prologue
open Silmaril Silmaril.X86

structure Plan where
  bytes : Nat
  alignment : Nat
  deriving DecidableEq, Repr

/-- The existing emitter may render arbitrary metadata. Operational alignment
uses explicit representable-immediate and power-of-two premises. -/
structure Valid (plan : Plan) : Prop where
  bytes : plan.bytes < 2147483648
  alignment : ∃ exponent < 32, plan.alignment = 2 ^ exponent

/-- Canonical signed immediate selection, matching the short form available
for the actual addition frame's 96-byte subtraction and -64 alignment mask. -/
def adjust (operation : Silmaril.X86.AluOp) (value : Int) : Ext.Instr :=
  if -128 ≤ value ∧ value ≤ 127 then
    .aluI8 .q operation (.reg .rsp) (BitVec.ofInt 8 value)
  else .aluI .q operation (.reg .rsp) (BitVec.ofInt 32 value)

def Plan.instructions (plan : Plan) : List Ext.Instr :=
  [.push .rbp, .mov .q (.reg .rbp) .rsp, adjust .sub plan.bytes, adjust .and (-(plan.alignment : Int))]

def slot (register : Nat) : Ext.Mem :=
  Ext.Mem.ofReg .rbp none (-(BitVec.ofNat 32 (8 * (register + 1))))

def frameInstructions (register : Nat) : List Ext.Instr :=
  [.mov .q (.reg .rax) .rsp, .mov .q (.mem (slot register)) .rax]

def Plan.activate (plan : Plan) (register : Nat) : List Ext.Instr :=
  plan.instructions ++ frameInstructions register

def Plan.code (plan : Plan) (register : Nat) : List Byte :=
  (plan.activate register).flatMap Ext.encode

/-- Exact original text, including whitespace and signed alignment spelling. -/
def Plan.render (plan : Plan) : String :=
  "  push rbp\n  mov rbp, rsp\n" ++
    s!"  sub rsp, {plan.bytes}\n  and rsp, {- (plan.alignment : Int)}\n"

def renderFrame (register : Nat) : String := "  mov rax, rsp\n" ++ Asm.write register

/-- Ordered real decoded-instruction execution. No alternative instruction
semantics or successful plan execution is built into the input domain. -/
inductive Executes : List Ext.Instr → X86.MState → X86.MState → Prop
  | nil (state) : Executes [] state state
  | cons (instruction : Ext.Instr) (rest : List Ext.Instr) (before middle after : X86.MState)
      (executed : Ext.exec instruction before.core before.memory = .ok middle.core middle.memory)
      (later : Executes rest middle after) : Executes (instruction :: rest) before after

def frameAddress (plan : Plan) (stack : Word) : Word :=
  (stack - 8 - BitVec.ofNat 64 plan.bytes) &&& BitVec.ofInt 64 (-(plan.alignment : Int))

/-- Exactly the two stores performed by the six-instruction activated prefix. -/
def footprint (stack : Word) (address : Nat) : Prop :=
  stack.toNat - 16 ≤ address ∧ address < stack.toNat

structure Entry (plan : Plan) (initial : X86.MState) : Prop where
  valid : Valid plan
  stackLower : 16 + plan.bytes + plan.alignment ≤ (initial.core.read .rsp).toNat
  readable : initial.memory.Permitted .read ((initial.core.read .rsp).toNat - 16) 16
  writable : initial.memory.Permitted .write ((initial.core.read .rsp).toNat - 16) 16

structure Ready (plan : Plan) (initial final : X86.MState) : Prop where
  pc : final.core.rip = initial.core.rip + BitVec.ofNat 64 (plan.code 0).length
  aligned : (final.core.read .rsp).toNat % plan.alignment = 0
  stack : final.core.read .rsp = frameAddress plan (initial.core.read .rsp)
  base : final.core.read .rbp = initial.core.read .rsp - 8
  accumulator : final.core.read .rax = frameAddress plan (initial.core.read .rsp)
  saved : final.memory.readBytes ((initial.core.read .rsp).toNat - 8) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [initial.core.read .rbp])
  reserved : final.memory.readBytes ((initial.core.read .rsp).toNat - 16) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [frameAddress plan (initial.core.read .rsp)])
  registers : ∀ register, register ≠ .rsp → register ≠ .rbp → register ≠ .rax →
    final.core.read register = initial.core.read register
  fsBase : final.core.fsBase = initial.core.fsBase
  frame : initial.memory.WritesWithin final.memory (footprint (initial.core.read .rsp))

end Silmaril.Compiler.Native.Emit.Prologue
