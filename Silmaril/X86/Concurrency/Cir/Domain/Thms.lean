module

public import Silmaril.X86.Concurrency.Cir.Thms
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Domain.Main

/-!
# Domain closure on CIR

PROVED (standard
axioms only; proofs in `Silmaril/Proofs/X86/Concurrency/Cir/Domain/`):

* `cirDomain`: `Task.cirDomain` holds. For a uniform program (`Prog.uniformB`), a
  domain closed under **partial** runs (`Prog.preClosedB`) and closed local blocks
  (`Prog.BlocksClosed`), every behaviour under SC, TSO or XL is a behaviour over that domain,
  by the same choice of runs and the same candidate execution;
* `behav_iff_behavIn`: so for such programs `Behav` and `BehavIn` over the domain are the same
  set of final states, and a verdict checked over the domain holds for all behaviours;
* `not_cirDomain_closedB`: the first statement, with `Prog.closedB` (values written by
  **complete** runs) in place of `preClosedB`, is false: `store x 7; load r x;
  loop 0 (r ≠ 7) skip` has no complete run over `[0]` (the loop is an `assume`), so `[0]` is
  `closedB`, but it has an SC behaviour that reads `7`;
* `not_cirDomain_preClosedB_without_blocksClosed`: `BlocksClosed` cannot be dropped
  from the restated Task either.

How it is proved: the rank argument, redone on CIR units (no access tears in a uniform
program, a read takes all its bytes from one write, induction along `(po ∪ rf)⁺`), with the
partial-run check supplying the value of each write from the prefix of its thread's run that
precedes it in `po`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus (Final Loc Model initByte Verdict Test)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- **Domain closure on CIR** (`Task.cirDomain`). -/
theorem cirDomain : Task.cirDomain :=
  Silmaril.Proofs.X86.Concurrency.Cir.Domain.cirDomain

/-- For a uniform program with a domain closed under partial runs and closed blocks, the
behaviours are the behaviours over the domain. -/
theorem behav_iff_behavIn {P : Prog} {dom : List Nat} (hU : P.uniformB = true)
    (hC : P.preClosedB dom = true) (hB : P.BlocksClosed dom) (M : Model) (f : Final) :
    Behav P M.Holds f ↔ BehavIn P dom M.Holds f :=
  ⟨cirDomain P dom hU hC hB M f, behavIn_behav⟩

/-- A `forbidden` verdict over the domain holds for all behaviours. -/
theorem forbidden_behav {P : Prog} {dom : List Nat} (hU : P.uniformB = true)
    (hC : P.preClosedB dom = true) (hB : P.BlocksClosed dom) (M : Model) {t : Test}
    (h : Verdict.forbidden.Holds t (BehavIn P dom M.Holds)) :
    Verdict.forbidden.Holds t (Behav P M.Holds) :=
  Silmaril.X86.MemoryModel.Litmus.forbidden_anti (fun f hf => cirDomain P dom hU hC hB M f hf) h

/-! ## The first statement was false -/

/-- The location `x` (one byte at `0`, initially `0`). -/
def Review.x : Loc := ⟨"x", 0, 1, 0⟩

/-- `store x 7; load rax x; loop 0 (rax ≠ 7) skip`: the bounded loop with bound `0` has a run
only if its condition is false, so it acts as `assume (rax = 7)`. -/
def Review.assume7 : Stmt :=
  .seq (.store .rlx 1 .wb (.lit 0) (.lit 7))
    (.seq (.load .rax .rlx 1 .wb (.lit 0)) (.loop 0 (.bin .ne (.reg .rax) (.lit 7)) .skip))

/-- One thread running `assume7`. -/
def Review.pA : Prog := Seq.solo [Review.x] Review.assume7

/-- **Domain closure fails with `closedB`**: `pA` is uniform, `[0]` is `closedB` for it (no run
over `[0]` completes, so it writes nothing) and blocks are closed, yet it has an SC behaviour
(reading `7`) and no behaviour over `[0]`. With `preClosedB` the partial run `store x 7` over
`[0]` writes `7`, so `[0]` is rejected. -/
theorem not_cirDomain_closedB :
    ¬ ∀ (P : Prog) (dom : List Nat), P.uniformB = true → P.closedB dom = true →
      P.BlocksClosed dom → ∀ (M : Model) (f : Final), Behav P M.Holds f →
        BehavIn P dom M.Holds f := by
  intro h
  have hU : Review.pA.uniformB = true := by decide +kernel
  have hC : Review.pA.closedB [0] = true := by decide +kernel
  have hB : Review.pA.BlocksClosed [0] := blocksClosed_of_noBlocks (by decide +kernel) _
  have hrun : ([Lab.wr .rlx .wb 0 1 7, Lab.rd .rlx .wb 0 1 7], Regs.zero.set .rax 7) ∈
      run [7] Review.assume7 Regs.zero := List.mem_singleton.mpr rfl
  have hs : SeqRun Review.assume7 Regs.zero (initByte [Review.x])
      [Lab.wr .rlx .wb 0 1 7, Lab.rd .rlx .wb 0 1 7] (Regs.zero.set .rax 7)
      (Mem.put (initByte [Review.x]) 0 1 7) := by
    refine ⟨⟨[7], hrun⟩, ?_⟩
    show (Lab.replay _ _).bind _ = _
    simp [Lab.replay, replay, Mem.val, Mem.put, Review.x, Silmaril.X86.MemoryModel.Litmus.leValue]
  have hb := Seq.solo_behav_complete [Review.x] Review.assume7 (by decide) (by decide)
    (MLe.refl Exec.Sc) hs
  obtain ⟨trs, hf, -⟩ := h Review.pA [0] hU hC hB .sc _ hb
  have h0 : Review.pA.traces [0] = [[]] := rfl
  rw [h0] at hf
  cases hf with
  | cons ha _ => simp at ha

/-- `[0]` is not closed under partial runs for `pA`. -/
theorem not_preClosed_assume7 : Review.pA.preClosedB [0] = false := by decide +kernel

/-- **`BlocksClosed` is still needed with `preClosedB`**: the program `p5` (one
block whose contract forces `rax = 5`, no locations) is uniform and `[0]` is closed under
partial runs for it (its block has no run over `[0]`), yet it has an SC behaviour over `[5]`
and none over `[0]`. -/
theorem not_cirDomain_preClosedB_without_blocksClosed :
    ¬ ∀ (P : Prog) (dom : List Nat), P.uniformB = true → P.preClosedB dom = true →
      ∀ (M : Model) (f : Final), Behav P M.Holds f → BehavIn P dom M.Holds f := by
  intro h
  have hU : Ex.p5.uniformB = true := by decide +kernel
  have hC : Ex.p5.preClosedB [0] = true := by decide +kernel
  have h5 : Ex.p5.traces [5] = [[Ex.tr5]] := rfl
  have h0 : Ex.p5.traces [0] = [[]] := rfl
  have hb : BehavIn Ex.p5 [5] Exec.Sc
      (Silmaril.X86.MemoryModel.Litmus.finalAx Ex.p5.memTest [Ex.tr5] { evs := [] }) := by
    refine ⟨[Ex.tr5], by rw [h5]; exact .cons (List.mem_singleton.mpr rfl) .nil, { evs := [] },
      rfl, rfl, by decide +kernel, fun r hr => absurd hr (Nat.not_lt_zero _), by decide +kernel,
      rfl⟩
  obtain ⟨trs, hf, -⟩ := h Ex.p5 [0] hU hC .sc _ ⟨[5], hb⟩
  rw [h0] at hf
  cases hf with
  | cons ha _ => simp at ha

end Silmaril.X86.Concurrency.Cir
