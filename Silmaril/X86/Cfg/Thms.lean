module

public import Silmaril.X86.Cfg.Defs
public import Silmaril.X86.Flow.Thms
import Silmaril.Proofs.X86.Cfg.Walk

/-!
# CFG certificates: the block decoder, target arithmetic, and a worked example

* `walk_cases`: one step of the block decoder.
* `ofNat_wrap`: a target computed by the checker (`wrap`) is the machine's sum.
* `tiny`: a three-block function (`xor %eax,%eax; test %rdi,%rdi; je; mov $39,%eax; syscall;
  ret`) whose certificate is exact by `decide`, with the `getpid` number read off the block's
  `rax` dataflow.
-/

@[expose] public section

namespace Silmaril.X86.Cfg

open Silmaril.X86 (Byte)
open Silmaril.X86.Flow (FlowDec)

variable {ε : Type}

/-- **One step of the block decoder.** -/
theorem walk_cases {D : FlowDec} {t : Term ε} {start fuel o : Nat} {v : Option Nat} {s : List Byte}
    (h : walk D t start fuel o v s = true) :
    ∃ i l, D.decode s = some (i, l) ∧ 0 < l ∧ l ≤ s.length ∧
      (D.kind i = .rep → D.rax i = .keep) ∧
      ((l = s.length ∧ termOk t (D.kind i) (start + o + l) v = true) ∨
       (l < s.length ∧ (D.kind i = .seq ∨ D.kind i = .rep) ∧
         ∃ fuel', walk D t start fuel' (o + l) (raxStep D v i) (s.drop l) = true)) :=
  Silmaril.Proofs.X86.Cfg.walk_cases h

/-- **A wrapped target is the machine's sum.** -/
theorem ofNat_wrap (n : Nat) (r : Int) :
    BitVec.ofNat 64 (wrap ((n : Int) + r)) = BitVec.ofNat 64 n + BitVec.ofInt 64 r :=
  Silmaril.Proofs.X86.Cfg.ofNat_wrap n r

/-! ## A worked example -/

/-- `xor %eax,%eax; test %rdi,%rdi; je 1f; mov $39,%eax; syscall; 1: ret` at `0x1000`. -/
def tiny : Graph Unit where
  entry := 0x1000
  blocks := [
    ⟨0x1000, [0x31, 0xC0, 0x48, 0x85, 0xFF, 0x74, 0x07], .jcc 0x100e 0x1007⟩,
    ⟨0x1007, [0xB8, 0x27, 0x00, 0x00, 0x00, 0x0F, 0x05], .sys (some 39) 0x100e⟩,
    ⟨0x100e, [0xC3], .ret⟩]

/-- `tiny` is the CFG of its bytes (`cfg_is`). -/
theorem tiny_exact : tiny.exact Flow.X64.dec = true := by decide

/-- A wrong system-call number is rejected. -/
example : (⟨0x1007, [0xB8, 0x27, 0x00, 0x00, 0x00, 0x0F, 0x05], .sys (some 57) 0x100e⟩ :
    Block Unit).ok Flow.X64.dec = false := by decide

end Silmaril.X86.Cfg
