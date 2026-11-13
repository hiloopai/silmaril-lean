module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Thread

/-!
# Proofs: the pool's CSL certificate, against the interface

`pool_proved`: for every pool meeting `Wp.Ok`, the pool's client is proved against the mutex
interface (`Mutex.Client.Proved`), with goal `Wp.goal`. The ghost start gives each worker its
private cell and the invariant the unlocked mutex next to `R` at the empty queue (every job
fresh). The goal follows from thread `0`'s postcondition `Q0` alone.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Concurrency.Cir.Mutex (Iface Client)
open Wp

/-- The workers' ghost start: each owns its private cell. -/
def hs0 (P : Wp) (t : Nat) : Heap := if t < P.K then Heap.single (P.cur t) 0 else Heap.empty

/-- `R` at the start: the empty queue, every job fresh. -/
def hR0 (P : Wp) : Heap := Heap.union (P.ctlH 0 0 0) (P.jobH fun _ => .fresh)

/-- The invariant's start: the unlocked mutex and `hR0`. -/
def hI0 (M : Iface) (P : Wp) : Heap := Heap.union (M.init P.m) (hR0 P)

variable {P : Wp}

theorem r0 : P.R (hR0 P) :=
  ⟨0, 0, 0, fun _ => .fresh, Nat.zero_le _, fun _ _ => ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩,
    doneCount_fresh.symm, rfl⟩

theorem cursH_cur {t : Nat} (ht : t < P.K) : P.cursH (P.cur t) = some 0 := by
  have : (List.range P.K).any (fun u => P.cur u == P.cur t) = true :=
    List.any_eq_true.mpr ⟨t, List.mem_range.mpr ht, by simp⟩
  simp [Wp.cursH, this]

theorem cursH_none {y : Nat} (h : ∀ t < P.K, y ≠ P.cur t) : P.cursH y = none := by
  have : (List.range P.K).any (fun u => P.cur u == y) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    obtain ⟨u, hu, e⟩ := List.any_eq_true.mp hh
    exact h u (List.mem_range.mp hu) (beq_iff_eq.mp e).symm
  simp [Wp.cursH, this]

variable (hP : P.Ok)
include hP

/-- A cell of the mutex object is outside every pool cell. -/
theorem init_out (M : Iface) (hM : M.size ≤ P.slot) {y : Nat} (hy : (M.init P.m y).isSome) :
    y ≠ P.qa ∧ y ≠ P.da ∧ y ≠ P.ea ∧ (∀ t < P.K, y ≠ P.cur t) ∧ P.owner y = none := by
  have hd := M.init_dom P.m y hy
  have out : ∀ a ∈ P.ctl, y ≠ a := fun a ha e => by
    have := (hP.ctlLt a ha).2; subst e; omega
  refine ⟨out _ (by simp [Wp.ctl]), out _ (by simp [Wp.ctl]), out _ (by simp [Wp.ctl]),
    fun t ht => out _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr ht))),
    ?_⟩
  cases ho : P.owner y with
  | none => rfl
  | some j =>
    have := (hP.fpLt j y (owner_spec ho).1).2
    omega

/-- **The ghost start is a CSL certificate** of the linked pool, for every mutex. -/
theorem ginv (M : Iface) (hM : M.size ≤ P.slot) (L : Nat) :
    GInv (Inv M P) (Qt P) P.K (P.client.link M L) (hs0 P) (hI0 M P) := by
  have F := ctlFacts hP
  have hmem : (P.client.link M L).mem =
      Heap.union P.mem0 (Heap.union (M.init P.m) Heap.empty) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u htu
    unfold hs0
    split
    · split
      · apply disjoint_of
        intro y hy
        simp only [single_apply] at hy ⊢
        split at hy
        · rename_i e; subst e
          simp only [ite_eq_right_iff]; intro e; exact absurd (cur_inj e) htu
        · simp at hy
      · exact disjoint_empty_right _
    · exact disjoint_empty _
  · intro t
    unfold hs0
    split
    · rename_i ht
      apply disjoint_of
      intro y hy
      simp only [single_apply] at hy
      split at hy
      · rename_i e; subst e
        have hi : M.init P.m (P.cur t) = none := by
          cases e : M.init P.m (P.cur t) with
          | none => rfl
          | some w => exact absurd rfl ((init_out hP M hM (by simp [e])).2.2.2.1 t ht)
        rw [hI0, union_none hi, hR0, union_or, ctlH_other (F.cq t ht) (F.cd t ht) (F.ce t ht),
          jobH_none (F.oc t ht)]
        rfl
      · simp at hy
    · exact disjoint_empty _
  · intro t y w hy
    unfold hs0 at hy
    split at hy
    · rename_i ht
      simp only [single_apply] at hy
      split at hy
      · rename_i e; subst e; cases hy
        rw [hmem, Wp.mem0, union_or, union_or, union_or,
          ctlH_other (F.cq t ht) (F.cd t ht) (F.ce t ht), cursH_cur ht]
        rfl
      · cases hy
    · cases hy
  · intro y w hy
    rw [hmem]
    simp only [hI0] at hy
    cases e : M.init P.m y with
    | some w' =>
      rw [union_some e] at hy; cases hy
      obtain ⟨h1, h2, h3, h4, h5⟩ := init_out hP M hM (y := y) (by rw [e]; rfl)
      have h0 : P.mem0 y = none := by
        rw [Wp.mem0, union_or, union_or, ctlH_other h1 h2 h3, cursH_none h4, jobH_none h5]
        rfl
      rw [union_none h0, union_some e]
    | none =>
      rw [union_none e, hR0, union_or] at hy
      apply union_some
      rw [Wp.mem0, union_or, union_or]
      cases e2 : P.ctlH 0 0 0 y with
      | some w' => rw [e2] at hy; simp only [Option.some_or] at hy ⊢; exact hy
      | none =>
        rw [e2] at hy
        simp only [Option.none_or] at hy ⊢
        obtain ⟨j, hj⟩ := jobH_some (P := P) (σ := fun _ => .fresh) (a := y) (by simp [hy])
        rw [cursH_none (owner_ne_ctl F hj).2.2.2]
        simpa using hy
  · refine sep_emp (M.init_inv P.m P.R (hR0 P) r0 ?_)
    apply disjoint_of
    intro y hy
    obtain ⟨h1, h2, h3, -, h5⟩ := init_out hP M hM hy
    rw [hR0, union_or, ctlH_other h1 h2 h3, jobH_none h5]
    rfl
  · intro t ht
    have : (P.client.link M L).ts t = (P.body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Client.link, Client.startWith, Wp.client, ht]
    rw [this]
    have : hs0 P t = Heap.single (P.cur t) 0 := by simp [hs0, ht]
    rw [this]
    exact thread_ok hP M L ht

/-- **The pool is proved against the mutex interface.** -/
theorem pool_proved : P.client.Proved P.goal := by
  intro M hM L
  refine ⟨Inv M P, Qt P, hs0 P, hI0 M P, ginv hP M hM L, ?_⟩
  intro rs mem hs' hI' hq _ hle _ it hit
  have h0 := hq 0 hP.kpos
  simp only [Qt, ite_true] at h0
  exact le_trans' (h0 it hit) (hle 0)

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
