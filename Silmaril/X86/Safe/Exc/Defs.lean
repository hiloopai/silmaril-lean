module

public import Silmaril.X86.Safe.Defs
public import Silmaril.X86.Sep.Extra.Defs
public import Silmaril.X86.Sep.SysV.Defs

/-!
# Two-exit triples: non-local exits (`setjmp`/`longjmp`)

A function that may `longjmp` has two exits: the **normal** one, where it returns as usual,
and the **exceptional** one, where control resumes at a continuation `k` saved by `setjmp`
(`rip = k.ret`, `rsp = k.sp`, the callee-saved registers equal to `k.cs`, `rax = v` with
`v ≠ 0`).

* `Cont`: a saved continuation, the contents of a System V `jmp_buf` (`Sep/JmpBuf`).
* `AtCont k v`: the machine is at the continuation `k` with `rax = v`: it owns `rip`, `rsp`,
  the callee-saved registers (with the values of `k`), `rax`, the other caller-saved
  registers and the flags.
* `Exc k E G`: the exceptional exit. Some `v ≠ 0`, `AtCont k v`, the exception payload `E v`,
  the **survivor frame** `G`, and garbage (`strue`): whatever the abandoned frames held.
* `STripleX I n P Q k E`: the two-exit step-indexed triple on the machine `I`. The frame is
  split in two: `F` is kept on the normal exit and *leaked* on the exceptional one (the
  abandoned stack frames between the `setjmp` caller and the `longjmp`), and `G` survives
  both. Every split is quantified, so a triple promises that nothing outside `P` changes on
  the normal exit, and that `G` survives the exceptional one.

The rules, including `STripleX.lift` along a machine extension, are in `Safe/Exc/Thms.lean`.

**Exceptional-exit ownership.** `AtCont` owns all sixteen general registers, `rip` and the
flags: that is what `longjmp` writes. A function whose two-exit triple may take the
exceptional exit therefore owns them in its precondition, so that they are in neither `F` nor
`G` (if `G` owned `rbx`, `G ∗ AtCont k v` would fail after `longjmp` restores `rbx`). This is
the price of `G` being arbitrary.
-/

@[expose] public section

namespace Silmaril.X86.Safe

open Silmaril.X86 (Word Reg)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Sep

/-- **A saved continuation** (a `jmp_buf`'s contents): the callee-saved registers
`rbx rbp r12 r13 r14 r15` of the `setjmp` caller, its stack pointer after `setjmp` returns,
and the return address of the `setjmp` call. -/
structure Cont where
  cs : List Word
  sp : Word
  ret : Word

/-- **The machine is at the continuation `k` with `rax = v`.** -/
def AtCont (k : Cont) (v : Word) : SProp :=
  ripPt k.ret ∗ regPt .rsp k.sp ∗ regsWith calleeSavedRegs k.cs ∗ regPt .rax v ∗
    regsAny clobberedRegs ∗ flagsAny

/-- **The exceptional exit** to `k` with payload `E`, keeping the survivor frame `G`. -/
def Exc (k : Cont) (E : Word → SProp) (G : SProp) : SProp :=
  sexists fun v => ⌜v ≠ 0⌝ ∗ AtCont k v ∗ E v ∗ G ∗ strue

variable {σ : Type} (I : Isa σ)

/-- **The two-exit step-indexed triple** on the machine `I`. From every live state whose
fragment splits as `P ∗ F ∗ G`, within `n` steps the machine does not get stuck before it
either returns normally (`Q ∗ F ∗ G`) or exits exceptionally to `k` (`Exc k E G`, leaking
`F`). -/
def STripleX (n : Nat) (P Q : SProp) (k : Cont) (E : Word → SProp) : Prop :=
  ∀ (F G : SProp) (s : σ), I.live s → (P ∗ F ∗ G) (frag I s) →
    SafeN I (fun t => (Q ∗ F ∗ G) (frag I t) ∨ Exc k E G (frag I t)) n s

end Silmaril.X86.Safe
