module

public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Seq.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Main
public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Review

/-!
# Localisation of owned regions

PROVED (standard axioms only):

* `cirLocalize`: **`Tv.Task.cirLocalize` holds** (proof in
  `Silmaril/Proofs/X86/Concurrency/Cir/Localize/`). An owned, futex-free, straight-line fragment
  of a thread, on cells below the ghost bytes that no other statement touches, may be replaced
  by a `local` block whose contract holds of the fragment's sequential runs: every behaviour
  under SC, TSO and XL (under XL: with write-back stores after the fragment) is a behaviour of
  the localised program with the same final memory and registers.
* `not_cirLocalize_futex`: the earlier statement (fragments with futex operations) is
  false;
* `not_cirLocalize_ghost`, `not_cirLocalize_wrap`, `not_cirLocalize_xlWeak`: the earlier statement
  (`Localize.CirLocalizeFirst`) is false; each counterexample breaks only one of the hypotheses
  added (footprint below `ctlAddr 0`; `Stmt.avoids` modulo `2 ^ 64`; write-back stores after the
  fragment under XL). Proofs in `Silmaril/Proofs/X86/Concurrency/Cir/Localize/Review.lean`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus (Final Loc Model initByte seqL)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.Concurrency.Cir.Tv (chain)

/-- **Localisation**. -/
theorem cirLocalize : Tv.Task.cirLocalize := Silmaril.Proofs.X86.Concurrency.Cir.Localize.cirLocalize

/-- The earlier statement is false: a location at a futex queue byte. -/
theorem not_cirLocalize_ghost : ¬ Silmaril.Proofs.X86.Concurrency.Cir.Localize.CirLocalizeFirst :=
  Silmaril.Proofs.X86.Concurrency.Cir.Localize.not_cirLocalizeFirst_ghost

/-- The earlier statement is false: a literal address `x + 2 ^ 64`. -/
theorem not_cirLocalize_wrap : ¬ Silmaril.Proofs.X86.Concurrency.Cir.Localize.CirLocalizeFirst :=
  Silmaril.Proofs.X86.Concurrency.Cir.Localize.not_cirLocalizeFirst_wrap

/-- The earlier statement is false: a non-temporal store after an `sfence` under XL. -/
theorem not_cirLocalize_xlWeak : ¬ Silmaril.Proofs.X86.Concurrency.Cir.Localize.CirLocalizeFirst :=
  Silmaril.Proofs.X86.Concurrency.Cir.Localize.not_cirLocalizeFirst_xlWeak

/-- A block with an empty footprint and a trivial contract. -/
def Review.nop : Block where
  name := "nop"
  ins := []
  outs := []
  rin := []
  rout := []
  spec := fun _ _ => True
  dec := fun _ _ => inferInstance

/-- The fragment: one futex wake on address `0` (its queue byte is `qAddr 0`). -/
def Review.wake : Stmt := .futexWake (.lit 0) (.lit 1)

/-- The first statement of `Tv.Task.cirLocalize` (before the futex and further hypotheses). -/
def Review.CirLocalizeOld : Prop :=
  ∀ (P : Prog) (i : Nat) (pre ops post : List Stmt) (B : Block),
    P.threads[i]? = some ⟨chain (pre ++ ops ++ post), false⟩ →
    B.cellsOk = true →
    (ops.all fun s => s.onCells (B.ins ++ B.outs) && s.storesWithin B.outs && s.threadFree) =
      true →
    (∀ c ∈ B.ins ++ B.outs, ∃ l ∈ P.locs, l.addr ≤ c.1 ∧ c.1 + c.2 ≤ l.addr + l.size) →
    ((pre ++ post).all (Stmt.avoids (B.ins ++ B.outs))) = true →
    (∀ j th, j ≠ i → P.threads[j]? = some th → th.body.avoids (B.ins ++ B.outs) = true) →
    (∀ s ∈ ops, ∀ r ∈ s.writes, r ∈ B.rout) →
    (∀ rs m tr rs' m', SeqRun (chain ops) rs m tr rs' m' →
      B.spec (B.rin.map (fun r => (rs r).toNat) ++ B.ins.map fun c => (m.val c.1 c.2).getD 0)
        (B.rout.map (fun r => (rs' r).toNat) ++ B.outs.map fun c => (m'.val c.1 c.2).getD 0)) →
    ∀ (M : Model) (f : Final), Behav P M.Holds f →
      ∃ f', Behav ⟨P.locs, P.threads.set i ⟨chain (pre ++ [.local B] ++ post), false⟩⟩ M.Holds f' ∧
        f'.mem = f.mem ∧ f'.regs = f.regs

/-- **The first `Task.cirLocalize` is false**: localising `futexWake 0 1` (one thread, no
locations) loses the write of `0` to its queue byte. -/
theorem not_cirLocalize_futex : ¬ Review.CirLocalizeOld := by
  intro h
  -- the program's sequential run: the wake reads `0` from the empty queue and writes `0`
  have hrun : ([Lab.fwake 0 1 0], Regs.zero) ∈ run [0] (chain [Review.wake]) Regs.zero :=
    List.mem_singleton.mpr rfl
  have hs : SeqRun (chain [Review.wake]) Regs.zero (initByte []) [Lab.fwake 0 1 0] Regs.zero
      (Mem.put (initByte []) (qAddr 0) 1 0) := by
    refine ⟨⟨[0], hrun⟩, ?_⟩
    show (Lab.replay _ _).bind _ = _
    simp [Lab.replay, replay, Mem.val, initByte, Silmaril.X86.MemoryModel.Litmus.leValue]
  have hb := Seq.solo_behav_complete [] (chain [Review.wake]) (by decide) (by decide)
    (MLe.refl Exec.Sc) hs
  obtain ⟨f', hf', hmem, -⟩ := h (Seq.solo [] (chain [Review.wake])) 0 [] [Review.wake] []
    Review.nop rfl (by decide) (by decide) (by simp [Review.nop]) (by decide)
    (fun j th hj hth => by
      cases j with
      | zero => exact absurd rfl hj
      | succ j => simp [Seq.solo] at hth)
    (fun s hs r hr => by simp [Review.wake] at hs; subst hs; simp [Stmt.writes] at hr)
    (fun _ _ _ _ _ _ => trivial) .sc _ hb
  -- every behaviour of the localised program leaves the queue byte unmapped
  replace hf' : Behav (Seq.solo [] (chain [.local Review.nop])) Model.sc.Holds f' := hf'
  obtain ⟨tr, rs, m, ⟨⟨dom, hdom⟩, hrep⟩, rfl⟩ := Seq.solo_behav_sound []
    (chain [.local Review.nop]) (by decide) (by decide) (M := Exec.Sc) sc_le_xl hf'
  have htr : tr = [Lab.blk "nop" [] [] []] := by
    simp [chain, run, runBlock, Res.bind, Review.nop, seqL, cellVals] at hdom
    exact hdom.1
  subst htr
  have hm : m = initByte [] := by
    simp [replay, Lab.replay] at hrep; exact hrep.symm
  subst hm
  have := congrFun hmem (qAddr 0)
  simp [Seq.soloFinal, Mem.put, initByte] at this

end Silmaril.X86.Concurrency.Cir
