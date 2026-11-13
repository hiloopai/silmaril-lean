module

public import Silmaril.Machine.X86.Lir.Image.Defs
public import Silmaril.Machine.CBackend.Lir.Backend.Defs

/-!
# The x86-64 backend as a refinement

`compile_refines` restates `compile_correct` in the behaviour layer (`Silmaril.Machine.CBackend.Behaviour.Refinement`):
under the premises of `compile_correct`, the machine `X86.Ext.sem` refines the
Lir semantics `Lir.sem p` in the mode `⟨.strict, .allowed⟩`, from every loaded
machine `(exit, E.load lm main args init)` paired with the Lir start state of
the same call.

The target counts a UD2 as exhaustion when it is at one of the stack-limit
checks of the compiled program with less stack left than the check requires
(`Ext.StackCheck.Exhausted S.stackLo E.stackSites`); every other UD2 is a trap.
The observation relates

* a returned machine state `final` to Lir values and memory `(vs, lm)` by
  `E.Final vs lm final`: values in `rax rdx`, callee-saved registers, RSP and
  RIP restored, `lm` represented;
* a trapped machine state `t` (at its UD2) to a Lir trap memory `lm` by
  `MemRel S lm t.memory`;
* no fault to anything (Lir has none).

What this says: from a loaded state whose Lir start state is safe, every
machine behaviour is a return with the observed values and memory of a Lir
return, a trap with the memory of a Lir trap, divergence of a diverging Lir
run, or exhaustion. A stop at a stack-limit check (`Env.Overflow`) is always
exhaustion (`Env.Overflow.exhausted`). A UD2 reached as a Lir trap that happens
to satisfy the stack-limit test is also reported as exhaustion; the mode admits
this, so in that case the trap is not reported as a trap. Exhaustion
implements every source outcome, so nothing is claimed for runs that exhaust
the stack. The proof is `Lir.Backend.refines_of_correct` applied to
`compile_correct`.
-/

@[expose] public section

namespace Silmaril.X86.Backend

open Silmaril.X86 (State MState Word Reg)
open Silmaril.Machine
open Relation

/-- **The x86-64 backend as a refinement.** Under the premises of
`compile_correct`, the machine with return address `exit` and the stack-limit
checks of the compiled program as exhaustion refines the Lir program, from
every loaded machine paired with the Lir start state of the same call. -/
theorem compile_refines {P : Type} [DecidableEq P] (A : Assign P) (p : Lir.Prog P) (S : Space)
    {img : Image} (hc : compile A p S.codeBase = .ok img) (hvalid : S.Valid img.code.length)
    (exit : Word) (E0 : Nat) (saved : Reg → Word) (hhi : E0 + 8 ≤ S.stackHi) (hlo : S.stackLo ≤ E0)
    (halign : E0 % 16 = 8)
    (hexit : exit.toNat < S.codeBase ∨ S.codeBase + img.code.length ≤ exit.toNat) :
    let E : Env P := ⟨A, p, S, exit, E0, saved⟩
    Behaviour.Refines ⟨.strict, .allowed⟩ (Ext.sem (Ext.StackCheck.Exhausted S.stackLo E.stackSites))
      (Lir.sem p)
      (fun t s => ∃ lm main args init, lm.size = S.memSize ∧ p.start main args lm = some s ∧
        t = (exit, E.load lm main args init))
      (fun _ _ => ⟨fun final (vs, lm) => E.Final vs lm final, fun t lm => MemRel S lm t.memory,
        fun _ e => e.elim⟩) := by
  intro E
  have correct : ∀ {lm main args init s}, lm.size = S.memSize → p.start main args lm = some s →
      _ := fun {lm main args init s} hsize hs =>
    (compile_correct A p S hc hvalid exit E0 saved hhi hlo halign hexit (lm := lm) (main := main)
      (args := args) (s₀ := s) hsize hs init).2.2
  refine Lir.Backend.refines_of_correct Ext.sem_deterministic
    (fun vs lm u => ∃ t, u = (exit, t) ∧
      ∃ final, Ext.step exit t = .returned final ∧ E.Final vs lm final)
    (fun lm u => ∃ t, u = (exit, t) ∧ Ext.step exit t = .trapped ∧ MemRel S lm t.memory)
    (fun u => ∃ t, u = (exit, t) ∧ E.Overflow t) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro - - - vs lm - ⟨t, rfl, final, hs, hf⟩
    exact ⟨final, .returned hs, hf⟩
  · rintro - - - lm - ⟨t, rfl, hs, hm⟩
    by_cases hx : Ext.StackCheck.Exhausted S.stackLo E.stackSites t
    · exact .inr (.exhausted hs hx)
    · exact .inl ⟨t, .trapped hs hx, hm⟩
  · rintro - ⟨t, rfl, hov⟩
    exact .exhausted hov.1 hov.exhausted
  · rintro - s ⟨lm, main, args, init, hsize, hs, rfl⟩ vs mem hb
    obtain ⟨u, hu, hr⟩ := (correct hsize hs).1 vs mem hb
    exact ⟨(exit, u), Ext.reach_of hu, hr.imp (⟨u, rfl, ·⟩) (⟨u, rfl, ·⟩)⟩
  · rintro - s ⟨lm, main, args, init, hsize, hs, rfl⟩ mem hb
    obtain ⟨u, hu, hr⟩ := (correct hsize hs).2.1 mem hb
    exact ⟨(exit, u), Ext.reach_of hu, hr.imp (⟨u, rfl, ·⟩) (⟨u, rfl, ·⟩)⟩
  · rintro - s ⟨lm, main, args, init, hsize, hs, rfl⟩ hd
    rcases (correct hsize hs).2.2 hd with hi | ⟨u, hu, hov⟩
    · exact .inl (Ext.infinite_of hi)
    · exact .inr ⟨(exit, u), Ext.reach_of hu, u, rfl, hov⟩

end Silmaril.X86.Backend
