module

import Silmaril.X86.Sse9.Thms
meta import Silmaril.X86.Sse9.Defs

/-! # Legacy XMM XOR regressions

The nonzero known answer was also checked with native `PXOR xmm0, xmm1` and
`XORPS xmm0, [aligned memory]`. See `docs/x86.md` for the fixture and commands.
-/

namespace Silmaril.X86.Sse9

open Silmaril.Process (Memory)

private def core : State :=
  { regs := fun _ => 0x20#64, rip := 0x1000#64, flags := ⟨none, none, none, none, none, none⟩ }

private def destValue : Xmm := 0x0123456789abcdeffedcba9876543210#128
private def sourceValue : Xmm := 0xffff0000aaaa55551122334455667788#128
private def answer : Xmm := 0xfedc4567230198baeffe89dc23324598#128

private def xmm : XFile := fun reg =>
  if reg = .xmm0 then destValue else if reg = .xmm1 then sourceValue else 0

private def noMem : Memory := ⟨[], ∅⟩
private def sourceMem : Memory :=
  ⟨[⟨0x20, 16, ⟨true, false, false⟩⟩],
    Memory.install ∅ 0x20 [0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
      0x55, 0x55, 0xaa, 0xaa, 0x00, 0x00, 0xff, 0xff]⟩

private def atRax : XRM := .mem (.ofReg .rax none 0)

private def destAfter : Except LogicalRefusal XResult → Option Xmm
  | .ok (.ok _ regs _) => some (regs .xmm0)
  | _ => none

example : decodeL [0x66, 0x0f, 0xef, 0xc1] = some ((Logical.Op.pxor).toInstr .xmm0 (.reg .xmm1), 4) :=
  by decide

example : decodeL [0x0f, 0x57, 0x00] = some ((Logical.Op.xorps).toInstr .xmm0 atRax, 3) := by decide

example : destAfter (execLogical ⟨true, true⟩ .pxor .xmm0 (.reg .xmm1) core xmm noMem 0x1004) =
    some answer := by decide

#guard destAfter (execLogical ⟨true, false⟩ .xorps .xmm0 atRax core xmm sourceMem 0x1003) == some answer

example : execLogical ⟨true, false⟩ .pxor .xmm0 atRax core xmm noMem 0x1004 =
    .error .featureDisabled := rfl

example : execLogical ⟨true, true⟩ .pxor .xmm0 atRax core xmm noMem 0x1004 = .ok .dataFault := rfl

example : execLogical ⟨true, true⟩ .pxor .xmm0 (.mem (.ofReg .rax none 1)) core xmm noMem 0x1004 =
    .ok .alignFault := rfl

example : decodeL [0xc5, 0xf9, 0xef, 0xc1] = none := by decide

#print axioms execLogical_of_read
#print axioms execLogical_enabled
#print axioms exec_pxor_self
#print axioms exec_xorps_self

end Silmaril.X86.Sse9
