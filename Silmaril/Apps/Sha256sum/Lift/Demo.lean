module


public import Silmaril.Apps.Sha256sum.Lift.Tactic

/-! # A first segment of `sha256sum-min`, by the VC generator (VERIFIED)

`start_segment`: from any state at `_start` (0x401000) whose memory holds the text, the
three instructions `xor %ebp,%ebp; mov %rsp,%rdi; and $-16,%rsp` reach the `call cmain` at
0x401009 with `rdi` the entry `rsp` and `rbp = 0`. The proof is the generic recipe:
`Lift.wp_instr hf hc rfl` (the instruction is found in the kernel-checked listing by `rfl`),
`x86_simp` (symbolic execution of `Ext8.exec` and evaluation of the cut test), `intro` of the
next state's `Code`. -/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift.Demo

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.Sys Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.X86 (Word State Reg)

/-- `_start`'s first three instructions, to the `call cmain` at 0x401009. -/
theorem start_segment {r11Of : Core → Word} {A : Machine} {E : Env} {k : KState} {a : A.State}
    (s : XState) (hf : s.faulted = false) (hc : Lift.Code s.memory)
    (hrip : s.core.rip = 0x401000#64) :
    wp (B := x86Machine8 r11Of) E
      (fun s' _ _ => s'.core.rip = 0x401009#64 ∧ s'.core.read .rdi = s.core.read .rsp ∧
        s'.core.read .rbp = 0)
      (fun s' => s'.core.rip.toNat == 0x401009) 10 s k a := by
  x86_step [hrip]
  x86_step [hrip]
  x86_step [hrip]
  show BitVec.setWidth 64 (BitVec.setWidth 32 (s.core.read Reg.rbp) ^^^
    BitVec.setWidth 32 (s.core.read Reg.rbp)) = 0#64
  simp

end Silmaril.Apps.Sha256sum.Lift.Demo
