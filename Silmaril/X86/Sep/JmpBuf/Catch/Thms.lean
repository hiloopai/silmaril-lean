module

public import Silmaril.X86.Sep.JmpBuf.Catch.Defs
public import Silmaril.X86.Sep.JmpBuf.Thms
import Silmaril.Proofs.X86.Sep.JmpBuf.Catch
import Silmaril.Proofs.X86.Sep.JmpBuf.Witness

/-!
# A worked example: `catch` returns `-1` through `longjmp`

* `catch_test`: on every machine `I` with `Open9.isa.Extends I`, at every index,
  `STriple I n (catchPre …) (catchPost …)`: `catch` returns to its caller with
  `eax = 0xffffffff` (`-1`), `rsp + 8` and the callee-saved registers. The proof builds
  two-exit triples of `throw1` and `throw2` with `xcall_rule` from `longjmp_triple`, and
  seals the exceptional exit of the protected region (`call throw2`) inside `catch` with
  `catch_rule`; the handler is the second return of `setjmp`. `catch_test_open9` is the
  instance at `Open9.isa`. This is step-indexed safety (partial correctness), as every
  `STriple`.
* **Non-vacuity**: `catchPre_m0`: the concrete state `m0` (the 122 bytes at `0x400000`,
  `rsp = 0x7000`, `rdi = 0x6000`, callee-saved registers `11 … 16`) meets `catchPre`;
  `catch_m0`: at every index the run from `m0` does not get stuck before `rip = 0x777777`,
  `rax = 0xffffffff`, `rsp = 0x7008` and the callee-saved registers `11 … 16`.
-/

@[expose] public section

namespace Silmaril.X86.Sep.JmpBuf.CatchTest

open Silmaril.X86 (MState Word)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.Safe

variable {σ : Type} {I : Isa σ}

/-- **`catch` returns `-1`**, on every machine extending `Open9.isa`. -/
theorem catch_test (E : Open9.isa.Extends I) (n : Nat)
    {e s r jb c0 c1 c2 c3 c4 c5 : Word} (h24 : 24 ≤ s.toNat)
    (he : e.toNat + 122 < 2 ^ 64) (hb : jb.toNat + 64 < 2 ^ 64) :
    STriple I n (catchPre e s r jb c0 c1 c2 c3 c4 c5) (catchPost s r c0 c1 c2 c3 c4 c5) :=
  Silmaril.Proofs.X86.Sep.JmpBuf.CatchTest.catch_test E n h24 he hb

/-- **`catch` returns `-1` on `Open9`.** -/
theorem catch_test_open9 (n : Nat) {e s r jb c0 c1 c2 c3 c4 c5 : Word} (h24 : 24 ≤ s.toNat)
    (he : e.toNat + 122 < 2 ^ 64) (hb : jb.toNat + 64 < 2 ^ 64) :
    STriple Open9.isa n (catchPre e s r jb c0 c1 c2 c3 c4 c5)
      (catchPost s r c0 c1 c2 c3 c4 c5) :=
  catch_test (Isa.Extends.refl _) n h24 he hb

/-- **The precondition is satisfiable**: it holds of a part of `m0`. -/
theorem catchPre_m0 :
    ∃ h, catchPre 0x400000 0x7000 RA 0x6000 11 12 13 14 15 16 h ∧ Frag.Le h (toFrag m0) :=
  Silmaril.Proofs.X86.Sep.JmpBuf.Witness.catchPre_m0

/-- **The example is not vacuous**: from the concrete state `m0`, `catch` returns `-1` with
`rsp + 8` and the callee-saved registers, at every index. -/
theorem catch_m0 (n : Nat) :
    SafeN Open9.isa (fun m =>
      m.core.rip = RA ∧ m.core.read .rax = 0xFFFFFFFF#64 ∧ m.core.read .rsp = 0x7008 ∧
      m.core.read .rbx = 11 ∧ m.core.read .rbp = 12 ∧ m.core.read .r12 = 13 ∧
      m.core.read .r13 = 14 ∧ m.core.read .r14 = 15 ∧ m.core.read .r15 = 16) n m0 :=
  Silmaril.Proofs.X86.Sep.JmpBuf.Witness.catch_m0 n

end Silmaril.X86.Sep.JmpBuf.CatchTest
