module

public import Silmaril.Process.ImageAccess.Defs
public import Silmaril.X86.Ext.Semantics

@[expose] public section

namespace Silmaril.Process.ImageAccess.X86

open Silmaril.X86 (Reg State)
open Silmaril.X86.Ext (Mem Sz leValue)

/-- A decoded `MOV` load. The core computes the data address from the incoming registers
and consumed length, but does not decide whether the address is visible or backed. -/
def load (size : Sz) (dest : Reg) (src : Mem) (core : State) (length : Nat) : Program State :=
  let next := core.rip + BitVec.ofNat 64 length
  .read ⟨.data, (src.addr core next).toNat, size.bytes⟩ fun bytes =>
    .done { size.write core dest ((BitVec.ofNat 64 (leValue bytes)).setWidth size.bits) with rip := next }

end Silmaril.Process.ImageAccess.X86
