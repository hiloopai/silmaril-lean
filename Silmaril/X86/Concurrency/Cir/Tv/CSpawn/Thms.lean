module

public import Silmaril.X86.Concurrency.Cir.Tv.CSpawn.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Marked.Thms
public import Silmaril.X86.Concurrency.Cir.Sync.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawn

/-!
# Spawn/join C litmus tests: what is proved

All statements are PROVED with the standard axioms. The per-test checks
are kernel `decide`s in `Silmaril/Proofs/X86/Concurrency/Cir/TvCSpawn.lean`.

The tests are five C programs from `examples/litmus-c/spawn`, each compiled by gcc 13.3 and
clang 23.1.3 (the pinned versions). gcc's `Counters` is refused by the proposer, because its
unlocked `addl $1, m` is not a form the checker accepts. That leaves nine tests:

* `MP+spawn`: data written before `spawn` is seen by the child (forbidden `r0 = 0`);
* `MP+join`: data written by the child is seen after `join` (forbidden `r0 = 0`);
* `Counters` (clang only): two children increment separate counters, one non-atomically and one
  with a relaxed `fetch_add`, and the parent reads both after joining both. Every outcome has
  `r0 = r1 = c1 = c2 = 1`;
* controls `MP+spawn-late` (spawn before the store) and `MP+nojoin` (read without join): `r0 = 0`
  is allowed even under SC, so the forbidden verdicts above come from spawn and join.

Results:

* `all_ok`, `all_transfer`: every test passes `CTest.allOk`, so each has `CTest.Transfer`:
  * x86 behaviours refine CIR behaviours;
  * the CIR program has the recorded SC, TSO and XL verdicts (and the recorded TSO verdict
    under operational TSO);
  * every `forbidden` verdict holds for the compiled x86 code.
* `all_sync`: the CIR verdicts also hold under the models with explicit spawn/join edges
  (`Exec.ScS`, `Exec.TsoS`, `Exec.XlS`).
* `mp_spawn_x86`, `mp_join_x86`, `counters_x86`: the forbidden verdicts for the compiled code of
  the three main tests, under XL (and so TSO and SC).
* `controls_allowed_sc`: the controls' witness is reachable for CIR under SC.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.CSpawn

open Silmaril.X86.MemoryModel.Litmus (Model Verdict Test Final)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- **Every C test passes.** -/
theorem all_ok : ∀ c ∈ all, c.allOk = true := Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawn.all_ok

/-- **Every C test transfers.** -/
theorem all_transfer : ∀ c ∈ all, c.Transfer := fun c hc => CTest.transfer_of_allOk (all_ok c hc)

theorem verdict_congr {v : Verdict} {t : Test} {R R' : Final → Prop} (h : ∀ f, R f ↔ R' f)
    (hv : v.Holds t R) : v.Holds t R' := by
  cases v <;> simp only [Verdict.Holds, Test.Allowed] at hv ⊢
  · obtain ⟨f, hf, hw⟩ := hv; exact ⟨f, (h f).mp hf, hw⟩
  · exact fun ⟨f, hf, hw⟩ => hv ⟨f, (h f).mpr hf, hw⟩

/-- **The verdicts hold under the models with explicit spawn/join edges.** -/
theorem all_sync : ∀ c ∈ all,
    (c.verdict .sc).Holds c.test (BehavIn c.prog c.dom Exec.ScS) ∧
      (c.verdict .tso).Holds c.test (BehavIn c.prog c.dom Exec.TsoS) ∧
      (c.verdict .xl).Holds c.test (BehavIn c.prog c.dom Exec.XlS) := by
  intro c hc
  have h := (all_transfer c hc).cir
  exact ⟨verdict_congr (fun _ => behavIn_scS_iff.symm) (h .sc),
    verdict_congr (fun _ => behavIn_tsoS_iff.symm) (h .tso),
    verdict_congr (fun _ => behavIn_xlS_iff.symm) (h .xl)⟩

theorem x86_of {c : CTest} (hc : c ∈ all) (hv : c.verdict .xl = .forbidden) :
    Verdict.forbidden.Holds c.test (c.XBehav Exec.Xl) :=
  (all_transfer c hc).x86_forbidden .xl hv

/-- **MP via spawn, on the compiled code**: the child never misses the data, under XL. -/
theorem mp_spawn_x86 :
    Verdict.forbidden.Holds «MP+spawn@gcc».test («MP+spawn@gcc».XBehav Exec.Xl) ∧
      Verdict.forbidden.Holds «MP+spawn@clang».test («MP+spawn@clang».XBehav Exec.Xl) :=
  ⟨x86_of (by simp [all]) rfl, x86_of (by simp [all]) rfl⟩

/-- **MP via join, on the compiled code**: the parent never misses the child's data after the
join, under XL. -/
theorem mp_join_x86 :
    Verdict.forbidden.Holds «MP+join@gcc».test («MP+join@gcc».XBehav Exec.Xl) ∧
      Verdict.forbidden.Holds «MP+join@clang».test («MP+join@clang».XBehav Exec.Xl) :=
  ⟨x86_of (by simp [all]) rfl, x86_of (by simp [all]) rfl⟩

/-- **Two children, separate counters, on the compiled code**: every outcome has both counters
and both reads equal to `1`, under XL. -/
theorem counters_x86 :
    Verdict.forbidden.Holds «Counters@clang».test («Counters@clang».XBehav Exec.Xl) :=
  x86_of (by simp [all]) rfl

/-- **The controls are allowed, even under SC** (for the CIR programs). -/
theorem controls_allowed_sc : ∀ c ∈ [«MP+spawn-late@gcc», «MP+spawn-late@clang»,
    «MP+nojoin@gcc», «MP+nojoin@clang»],
    Verdict.allowed.Holds c.test (BehavIn c.prog c.dom Exec.Sc) := by
  intro c hc
  have hc' : c ∈ all := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hc; simp only [all]; aesop
  have := (all_transfer c hc').cir .sc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact this

end Silmaril.X86.Concurrency.Cir.Tv.CSpawn
