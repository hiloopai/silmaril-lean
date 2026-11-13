module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Erase

/-!
# Proofs: `Drop2` finishes (non-vacuity)

`drop2_buffered` and `drop2_phys` speak about finished, drained states. This file shows that
such states exist: `drop2_finishes` is an explicit TSO run of `Drop2` with the leaking allocator
from the physical start, thread `0` then thread `1`, that ends finished and drained. It is built
on the four client cells (`small`) and moved to the physical start by `oreach_mono`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Rc.Drop2

theorem touches_rd' {m : Mode} {fl : Flav} {a sz v x : Nat} :
    Lab.Touches (.rd m fl a sz v) x ↔ x = a := by
  simp [Lab.Touches, Lab.reads, Lab.wval]

theorem touches_wr' {m : Mode} {fl : Flav} {a sz v x : Nat} :
    Lab.Touches (.wr m fl a sz v) x ↔ x = a := by
  by_cases h : a = x
  · simp [Lab.Touches, Lab.reads, Lab.wval, h]
  · simp [Lab.Touches, Lab.reads, Lab.wval, h]; omega

theorem touches_rmw' {m : Mode} {a sz o n x : Nat} :
    Lab.Touches (.rmw m a sz o n) x ↔ x = a := by
  by_cases h : a = x <;> simp [Lab.Touches, Lab.reads, Lab.wval, h]

theorem touches_fence' {k : Silmaril.X86.Atomic9.FenceKind} {x : Nat} :
    ¬ Lab.Touches (.fence k) x := by
  simp [Lab.Touches, Lab.reads, Lab.wval]

/-- The four client cells: count `2`, payload `42`, both outputs `0`. -/
def small : Heap := fun x =>
  if x = 0x100 then some 2 else if x = 0x104 then some 42 else
  if x = 0x200 then some 0 else if x = 0x208 then some 0 else none

/-- The start's threads on the four client cells. -/
def smallStart : OCfg := ⟨(start leakAlloc Heap.empty Heap.empty).ts, small, fun _ => []⟩

set_option maxRecDepth 4096 in
/-- **An explicit finished, drained TSO run** on the four client cells. -/
theorem small_run : ∃ C : OCfg, OReach .tso 2 smallStart C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) := by
  refine ⟨_,
    -- thread 0: clone (count 2 → 3), read 42, publish, flush, drop (3 → 2), drop (2 → 1)
    Star.step (OStep.drained (t := 0) (by decide) (TStep.seq (TStep.rmw (old := 2) (by decide)))
      rfl rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 0) (by decide)
      (TStep.seq (TStep.load (v := 42) (by decide))) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 0) (by decide) (TStep.seq TStep.store) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.flush (t := 0) (pre := []) (e := .st 0x200 42 false) (post := [])
      (by decide) ?_ ?_ (Or.inr rfl))
    (Star.step (OStep.drained (t := 0) (by decide)
      (TStep.seq (TStep.seq (TStep.rmw (old := 3) (by decide)))) rfl rfl ?_ ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) (TStep.seq TStep.seqSkip))
    (Star.step (OStep.tau (t := 0) (by decide) (TStep.seq (TStep.iteF ?_)))
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.drained (t := 0) (by decide) (TStep.seq (TStep.rmw (old := 2) (by decide)))
      rfl rfl ?_ ?_ ?_)
    (Star.step (OStep.tau (t := 0) (by decide) TStep.seqSkip)
    (Star.step (OStep.tau (t := 0) (by decide) (TStep.iteF ?_))
    -- thread 1: clone (1 → 2), read 42, publish, flush, drop (2 → 1), drop (1 → 0): cold path
    (Star.step (OStep.drained (t := 1) (by decide) (TStep.seq (TStep.rmw (old := 1) (by decide)))
      rfl rfl ?_ ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 1) (by decide)
      (TStep.seq (TStep.load (v := 42) (by decide))) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.buffered (t := 1) (by decide) (TStep.seq TStep.store) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.flush (t := 1) (pre := []) (e := .st 0x208 42 false) (post := [])
      (by decide) ?_ ?_ (Or.inr rfl))
    (Star.step (OStep.drained (t := 1) (by decide)
      (TStep.seq (TStep.seq (TStep.rmw (old := 2) (by decide)))) rfl rfl ?_ ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) (TStep.seq TStep.seqSkip))
    (Star.step (OStep.tau (t := 1) (by decide) (TStep.seq (TStep.iteF ?_)))
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.drained (t := 1) (by decide) (TStep.seq (TStep.rmw (old := 1) (by decide)))
      rfl rfl ?_ ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.tau (t := 1) (by decide) (TStep.iteT ?_))
    -- the cold path: overwrite the payload, flush, `rdi := l`, free (`mfence`)
    (Star.step (OStep.buffered (t := 1) (by decide) (TStep.seq TStep.store) rfl rfl ?_ ?_)
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.flush (t := 1) (pre := []) (e := .st 0x104 0 false) (post := [])
      (by decide) ?_ ?_ (Or.inr rfl))
    (Star.step (OStep.tau (t := 1) (by decide) (TStep.seq TStep.assign))
    (Star.step (OStep.tau (t := 1) (by decide) TStep.seqSkip)
    (Star.step (OStep.drained (t := 1) (by decide) TStep.fence rfl rfl ?_ ?_ ?_)
    Star.refl))))))))))))))))))))))))))))))))), ?_, ?_⟩
  all_goals first
    | rfl
    | (intro a ta; rw [touches_wr'.mp ta]; decide +kernel)
    | (intro a ta; rw [touches_rd'.mp ta]; decide +kernel)
    | (intro a ta; rw [touches_rmw'.mp ta]; decide +kernel)
    | (intro a ta; exact absurd ta touches_fence')
    | (intro p hp; simp only [Lab.reads, List.mem_singleton] at hp; subst hp; decide +kernel)
    | (intro p hp; simp [Lab.reads] at hp)
    | (intro t ht; have : t = 0 ∨ t = 1 := by omega
       rcases this with rfl | rfl <;> simp [upd])
    | (intro t
       by_cases h0 : t = 0
       · subst h0; rfl
       · by_cases h1 : t = 1
         · subst h1; rfl
         · simp [upd, h0, h1, smallStart])

theorem small_le : Heap.Le small (startPhys leakAlloc Heap.empty Heap.empty).mem := by
  intro a v h
  simp only [small] at h
  by_cases h1 : a = 0x100
  · subst h1; cases h; decide +kernel
  by_cases h2 : a = 0x104
  · subst h2; cases h; decide +kernel
  by_cases h3 : a = 0x200
  · subst h3; cases h; decide +kernel
  by_cases h4 : a = 0x208
  · subst h4; cases h; decide +kernel
  simp [h1, h2, h3, h4] at h

/-- **`Drop2` finishes**: from the physical start with the leaking allocator, some TSO run
(hence an XL run) ends finished and drained, so `drop2_phys` and `drop2_buffered` are not
vacuous. -/
theorem drop2_finishes : ∃ C : OCfg,
    OReach .tso 2 (startPhys leakAlloc Heap.empty Heap.empty).toO C ∧ C.Drained ∧
      (∀ t < 2, (C.ts t).1 = .skip) := by
  obtain ⟨C, hr, hd, hf⟩ := small_run
  obtain ⟨m', hr', -⟩ := oreach_mono hr small_le
  exact ⟨⟨C.ts, m', C.buf⟩, hr', hd, hf⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
