module

public import Silmaril.Compiler.Native.Correctness.LiteralImage.Defs
public import Silmaril.X86.Ext.SymExec
public import Silmaril.Machine.C.Api.SysV.Defs
/-! Caller-parametric conditions and the actual architectural result of the
shared literal image. The domain inspects code bytes, permissions, stack bounds,
alignment and separation; it assumes no successful run or returned value.
This machine omits DF and the Ffi x87-mode bit, so this is an integer System V
boundary with actual vector/control-state preservation, not full Ffi.Return.
-/

@[expose] public section
namespace Silmaril.Compiler.Native.Correctness.LiteralCaller
open Silmaril Silmaril.X86
open Silmaril.Compiler.Native.Correctness

/-- A 48-byte work span containing all five eight-byte stores.
The aligned RSP may be lower; no byte at that lower address is accessed. -/
def footprint (sp : Word) (address : Nat) : Prop :=
  sp.toNat - 48 ≤ address ∧ address < sp.toNat

structure Entry (base exit : Word) (initial : X86.MState) : Prop where
  pc : initial.core.rip = base
  image : Ext.Loaded initial.memory base LiteralImage.code
  stackLower : 128 ≤ (initial.core.read .rsp).toNat
  stackUpper : (initial.core.read .rsp).toNat + 8 < 2 ^ 64
  alignment : ((initial.core.read .rsp).toNat + 8) % 16 = 0
  stackRead : initial.memory.Permitted .read ((initial.core.read .rsp).toNat - 48) 56
  stackWrite : initial.memory.Permitted .write ((initial.core.read .rsp).toNat - 48) 48
  returnAddress : initial.memory.readBytes (initial.core.read .rsp).toNat 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [exit])
  separate : base.toNat + LiteralImage.code.length ≤ (initial.core.read .rsp).toNat - 48 ∨
    (initial.core.read .rsp).toNat ≤ base.toNat

def alignedFlags (sp : Word) : Flags := Ext.AluOp.flagsN .and (sp - 56) (0xffffffffffffffc0 : Word)
/-- The five eight-byte stores leave the eight-byte hole at RSP−24 untouched. -/
def writeFootprint (sp : Word) (address : Nat) : Prop :=
  (sp.toNat - 48 ≤ address ∧ address < sp.toNat - 24) ∨
    (sp.toNat - 16 ≤ address ∧ address < sp.toNat)
structure Result (exit : Word) (initial final : NativeState) : Prop where
  pc : final.state.core.rip = exit
  stack : final.state.core.read .rsp = initial.state.core.read .rsp + 8
  value : final.state.core.read .rax = 42
  registers : ∀ r, r ≠ .rsp → r ≠ .rax → final.state.core.read r = initial.state.core.read r
  fsBase : final.state.core.fsBase = initial.state.core.fsBase
  vectors : final.state.zmm = initial.state.zmm
  masks : final.state.k = initial.state.k
  mxcsr : final.state.mxcsr = initial.state.mxcsr
  x87 : final.state.x87 = initial.state.x87
  flags : final.state.core.flags = alignedFlags (initial.state.core.read .rsp)
  frame : initial.memory.WritesWithin final.memory (writeFootprint (initial.state.core.read .rsp))

end Silmaril.Compiler.Native.Correctness.LiteralCaller
