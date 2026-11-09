module

public import Silmaril.X86.Sep.JmpBuf.Defs
public import Silmaril.X86.Safe.Exc.Thms
public import Silmaril.X86.Sep.Insn.Thms
public import Silmaril.X86.Sep.Ind.Thms
import Silmaril.Proofs.X86.Sep.JmpBuf.Setjmp
import Silmaril.Proofs.X86.Sep.JmpBuf.Longjmp

/-!
# `setjmp`/`longjmp`: theorems

* `setjmp_triple`: `setjmp` (43 bytes, `setjmpBytes`) as a total triple on every machine `I`
  with `Open.isa.Extends I`. From `rdi = bw` with `jbAny bw` and the return address `ret` at
  `sp`, it returns to `ret` with `rsp = sp + 8`, `rax = 0`, the callee-saved registers
  unchanged and `jbPt bw (saved cs sp ret)`. Its postcondition mentions its own `sp` and
  `ret`, which `FnSpec` cannot express, so it is a raw triple.
* `longjmp_triple`: `longjmp` (41 bytes, `longjmpBytes`) as an exceptional-only `STripleX`
  on every machine `I` with `Open9.isa.Extends I` (its last instruction, `jmp *0x38(%rdi)`,
  is an `Ext9` form): for every index and every normal postcondition, it exits to the
  continuation in the `jmp_buf` with `rax = retVal v ≠ 0`; the payload returns the code and
  the `jmp_buf`.
* `jbPt_words` (a `jmp_buf` is eight words), `jbAny_split`, `retVal_ne_zero`.

Both triples assume no address wrap-around of the code and the `jmp_buf`
(`e.toNat + 43 < 2 ^ 64`, `bw.toNat + 64 < 2 ^ 64`). The instruction triples they are built
from are in `Sep/Insn`; a worked example (`catch → throw2 → throw1 → longjmp`, sealed by
`catch_rule`) is in `Sep/JmpBuf/Catch`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.JmpBuf

open Silmaril.X86 (MState Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Safe

variable {σ : Type} {I : Isa σ}

/-- **`setjmp`**: save the callee-saved registers, the stack pointer after return and the
return address into the `jmp_buf`, and return `0`. -/
theorem setjmp_triple (E : Open.isa.Extends I) {e sp ret bw c0 c1 c2 c3 c4 c5 : Word}
    (he : e.toNat + 43 < 2 ^ 64) (hb : bw.toNat + 64 < 2 ^ 64) :
    Triple I
      (codePt e.toNat setjmpBytes ∗ ripPt e ∗ regPt .rsp sp ∗ wordPt sp.toNat ret ∗
        regPt .rdi bw ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regAny .rdx ∗
        regAny .rax ∗ flagsAny ∗ jbAny bw.toNat)
      (codePt e.toNat setjmpBytes ∗ ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ wordPt sp.toNat ret ∗
        regPt .rdi bw ∗ regsWith calleeSavedRegs [c0, c1, c2, c3, c4, c5] ∗ regPt .rdx ret ∗
        regPt .rax 0 ∗ flagsAny ∗ jbPt bw.toNat (saved [c0, c1, c2, c3, c4, c5] sp ret)) :=
  (Silmaril.Proofs.X86.Sep.JmpBuf.setjmp_triple he hb).lift E

/-- **`longjmp`**: called with `rdi = bw`, a `jmp_buf` holding the continuation `k`, and
`rsi = v`, it restores `k`'s callee-saved registers and stack pointer and jumps to `k.ret`
with `rax = retVal v` (`v` as an `int`, `1` if it is `0`). The normal exit is never taken,
so `Q` is arbitrary. The precondition owns every register `AtCont` mentions. -/
theorem longjmp_triple (E : Open9.isa.Extends I) {l bw v c0 c1 c2 c3 c4 c5 ksp kret : Word}
    (hl : l.toNat + 41 < 2 ^ 64) (hb : bw.toNat + 64 < 2 ^ 64) (Q : SProp) (n : Nat) :
    STripleX I n
      (codePt l.toNat longjmpBytes ∗ ripPt l ∗ regPt .rdi bw ∗ regPt .rsi v ∗ regAny .rax ∗
        flagsAny ∗ regsAny calleeSavedRegs ∗ regAny .rsp ∗
        regsAny [.rcx, .rdx, .r8, .r9, .r10, .r11] ∗
        jbPt bw.toNat ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩)
      Q ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩
      (fun v' => ⌜v' = retVal v⌝ ∗ codePt l.toNat longjmpBytes ∗
        jbPt bw.toNat ⟨[c0, c1, c2, c3, c4, c5], ksp, kret⟩) :=
  Silmaril.Proofs.X86.Sep.JmpBuf.longjmp_triple E hl hb Q n

/-- **A `jmp_buf` holding `k` is eight words.** -/
theorem jbPt_words (b : Nat) (c0 c1 c2 c3 c4 c5 sp ret : Word) :
    jbPt b ⟨[c0, c1, c2, c3, c4, c5], sp, ret⟩ =
      (wordPt b c0 ∗ wordPt (b + 8) c1 ∗ wordPt (b + 16) c2 ∗ wordPt (b + 24) c3 ∗
        wordPt (b + 32) c4 ∗ wordPt (b + 40) c5 ∗ wordPt (b + 48) sp ∗ wordPt (b + 56) ret) :=
  Silmaril.Proofs.X86.Sep.JmpBuf.jbPt_words b c0 c1 c2 c3 c4 c5 sp ret

/-- The 64 bytes of a `jmp_buf` as eight blocks. -/
theorem jbAny_split (b : Nat) :
    jbAny b = (blockAny b 8 ∗ blockAny (b + 8) 8 ∗ blockAny (b + 16) 8 ∗ blockAny (b + 24) 8 ∗
      blockAny (b + 32) 8 ∗ blockAny (b + 40) 8 ∗ blockAny (b + 48) 8 ∗ blockAny (b + 56) 8) :=
  Silmaril.Proofs.X86.Sep.JmpBuf.jbAny_split b

/-- `longjmp(b, v)` never makes `setjmp` return `0`. -/
theorem retVal_ne_zero (v : Word) : retVal v ≠ 0 :=
  Silmaril.Proofs.X86.Sep.JmpBuf.retVal_ne_zero v

end Silmaril.X86.Sep.JmpBuf
