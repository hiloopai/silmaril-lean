module

public import Silmaril.Machine.X86.Decompile.Features.Defs

/-! A separate single-instruction LEA32 byte check. The general SemLift checker
continues to reject this instruction; no imported checker or machine is changed. -/
@[expose] public section
namespace Silmaril.Machine.X86.Decompile.Lea32
open Silmaril Silmaril.X86

def check (bytes : List Byte) (destination : Reg) (address : Ext.Mem) (length : Nat) : Bool :=
  decide (Ext.decode bytes = some (.lea .d destination address, length))

def next (machine : X86.MState) (destination : Reg) (address : Ext.Mem) (length : Nat) : X86.MState :=
  let pc := machine.core.rip + BitVec.ofNat 64 length
  ⟨{ machine.core.write destination (((address.addr machine.core pc).setWidth 32).setWidth 64)
    with rip := pc }, machine.memory⟩

end Silmaril.Machine.X86.Decompile.Lea32
