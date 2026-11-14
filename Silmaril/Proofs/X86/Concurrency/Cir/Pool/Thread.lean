module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Worker

/-!
# Proofs: one thread of the pool is safe, for every mutex

The invariant is `M.inv m R ∗ emp`, for any `M : Mutex.Iface`. Only the interface's fields are
used (through `safe_lock`, `safe_unlock`, `safe_crit`), never `M`'s code.

* `wbody_ok`, `worker_ok`: a worker owning only its private cell stays so, round after round;
* `waitL_ok`: thread `0`'s wait ends, if it ends, holding every job's done cells (`Q0`);
* `thread_ok`: thread `t`'s whole body, with postcondition `Q0` for `t = 0` and `True` else.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Concurrency.Cir.Mutex (Iface)
open Wp

/-- The pool's invariant at the mutex `M`. -/
abbrev Inv (M : Iface) (P : Wp) : HProp := M.inv P.m P.R ∗ hemp

/-- A worker owns its private cell. -/
def Own (P : Wp) (t : Nat) : Regs → HProp := fun _ h => ∃ v, h = Heap.single (P.cur t) v

/-- **Thread `0`'s postcondition**: every job's done cells. -/
def Q0 (P : Wp) : Regs → HProp := fun _ h => ∀ it ∈ P.items, Heap.Le it.doneH h

/-- The postcondition of thread `t`. -/
def Qt (P : Wp) (t : Nat) : Regs → HProp := if t = 0 then Q0 P else fun _ _ => True

variable {P : Wp} (hP : P.Ok) (M : Iface) (L : Nat)
include hP

theorem tail_ok {t : Nat} (ht : t < P.K) (rs : Regs) (v : Nat) :
    Csl.Safe (Inv M P) (Own P t)
      (.seq (ldc .r12 (P.cur t)) (.assign .r13 (.bin .ltu (.reg .r12) (.lit P.n)))) rs
      (Heap.single (P.cur t) v) := by
  apply safe_seq
  apply safe_ld ((ctlFacts hP).lc t ht) (v := v) (by simp [single_apply])
  exact safe_assign ⟨v, rfl⟩

/-- **One round of a worker.** -/
theorem wbody_ok {t : Nat} (ht : t < P.K) (rs : Regs) (v : Nat) :
    Csl.Safe (Inv M P) (Own P t) (P.wbody (M.lock L) (M.unlock L) t) rs
      (Heap.single (P.cur t) v) := by
  have F := ctlFacts hP
  have hn := hP.nlt
  unfold Wp.wbody Wp.crit
  apply safe_seq
  refine safe_crit M L hP.mlt (G := GT P t) (fun rs' hR r _ => take_ok hP ht rs' r)
    (fun rs' ho' g => ?_)
  apply safe_skip
  rcases g with ⟨k, hk, rfl⟩ | rfl
  · have hcur : P.stH k .fresh (P.cur t) = none :=
      stH_none hP (by simp [F.oc t ht])
    apply safe_seq
    apply safe_ld (F.lc t ht) (v := k) (by rw [union_none hcur]; simp [single_apply])
    apply safe_seq
    apply safe_ite
    · intro hc
      apply safe_seq
      refine safe_disp (k := k) (by omega) P.items 0 (rs'.set .r12 (BitVec.ofNat 64 k))
        (by simp [Regs.set]) (Nat.zero_le _)
        (by simp [Wp.n] at hk ⊢; omega) (by have := hP.nlt; simp [Wp.n] at this ⊢; omega)
        (fun it e => ?_)
      simp only [Nat.sub_zero] at e
      have hit : P.items[k]'hk = it := by
        rw [List.getElem?_eq_getElem hk] at e; exact Option.some.inj e
      have hmem : it ∈ P.items := hit ▸ List.getElem_mem hk
      have hfp : ∀ a, P.fpB k a = true → a < 2 ^ 64 := fun a h => (hP.fpLt k a h).1
      have hcnt : it.cnt < 2 ^ 64 := hfp _ (hit ▸ fpB_cnt hk)
      rw [stH_of_lt hk, hit]
      rw [stH_of_lt hk, hit] at hcur
      simp only [Item.stH] at hcur
      have H1 := safe_frame (F := fun h => h = Heap.single (P.cur t) k)
        (safe_run (I := Inv M P) (hP.argLen it hmem) hcnt (rs'.set .r12 (BitVec.ofNat 64 k)))
        (disjoint_of fun y hy => by
          rw [single_apply]
          split
          · rename_i e; subst e; rw [hcur] at hy; simp at hy
          · rfl) rfl
      refine safe_conseq (fun rs2 h hp => ?_) H1
      obtain ⟨h1, h2, d12, rfl, rfl, rfl⟩ := sep_iff.mp hp
      refine safe_crit M L hP.mlt (G := GR P t) (fun rs3 hR r d => ?_) (fun rs3 ho g => ?_)
      · have := ret_ok (I := Inv M P) hP ht hk rs3 r (by rw [stH_of_lt hk, hit]; exact d)
        rw [stH_of_lt hk, hit] at this
        exact this
      · apply safe_skip
        obtain ⟨w, rfl⟩ := g
        exact tail_ok hP M ht _ w
    · intro hc
      rw [ltu_eval (k := k) (by simp [Regs.set]) (by omega) (by omega)] at hc
      simp at hc; omega
  · apply safe_seq
    apply safe_ld (F.lc t ht) (v := P.n) (by simp [single_apply])
    apply safe_seq
    apply safe_ite
    · intro hc
      rw [ltu_eval (k := P.n) (by simp [Regs.set]) (by omega) (by omega)] at hc
      simp at hc
    · intro _
      exact safe_skip (tail_ok hP M ht _ _)

/-- **A worker**: every round keeps it owning just its private cell. -/
theorem worker_ok {t : Nat} (ht : t < P.K) (rs : Regs) (v : Nat) :
    Csl.Safe (Inv M P) (Own P t) (P.worker (M.lock L) (M.unlock L) t) rs
      (Heap.single (P.cur t) v) := by
  unfold Wp.worker
  apply safe_seq
  apply safe_assign
  exact safe_loop (fun _ _ h => ∃ v, h = Heap.single (P.cur t) v) (fun _ _ _ h _ => h)
    (fun _ rs h hJ _ => by obtain ⟨w, rfl⟩ := hJ; exact wbody_ok hP M L ht rs w) ⟨v, rfl⟩

/-- The wait loop's invariant. -/
def WJ (P : Wp) (_ : Nat) (rs : Regs) (h : Heap) : Prop :=
  (truthy (rs .r14) = true ∧ ∃ v, h = Heap.single (P.cur 0) v) ∨
    (truthy (rs .r14) = false ∧ Q0 P rs h)

/-- **Thread `0`'s wait**: if it stops, it holds every job's done cells. -/
theorem waitL_ok (rs : Regs) (v : Nat) :
    Csl.Safe (Inv M P) (Q0 P) (P.waitL (M.lock L) (M.unlock L)) rs
      (Heap.single (P.cur 0) v) := by
  have F := ctlFacts hP
  have hn := hP.nlt
  have hk0 := hP.kpos
  have hK := hP.klt
  unfold Wp.waitL
  apply safe_seq
  apply safe_assign
  refine safe_loop (WJ P) (fun _ rs h hJ hc => ?_) (fun _ rs h hJ hc => ?_)
    (Or.inl ⟨by simp [Regs.set, Expr.eval, truthy], v, rfl⟩)
  · rcases hJ with ⟨h1, -⟩ | ⟨-, hq⟩
    · simp [Expr.eval] at hc; rw [hc] at h1; cases h1
    · exact hq
  · rcases hJ with ⟨-, w, rfl⟩ | ⟨h1, -⟩
    swap
    · simp [Expr.eval] at hc; rw [hc] at h1; cases h1
    unfold Wp.waitB
    apply safe_lock M L hP.mlt
    intro rs' hR htok r tk d1 d2
    obtain ⟨k', d, e, σ, hk', hfr, hd, rfl⟩ := r
    have hdn : d ≤ P.n := hd ▸ doneCount_le σ
    apply safe_seq
    apply safe_ld F.ld (v := d)
      (by rw [union_or, union_or, union_or, ctlH_eq]; simp [Ne.symm F.qd])
    apply safe_seq
    apply safe_ld F.le (v := e)
      (by rw [union_or, union_or, union_or, ctlH_eq]; simp [Ne.symm F.qe, Ne.symm F.de])
    apply safe_ite
    · intro hc
      have hb : BitVec.ofNat 64 d = BitVec.ofNat 64 P.n := by
        have := and_eq_eval hc
        simpa [Regs.set] using this
      have hdn' : d = P.n := by
        have := congrArg BitVec.toNat hb
        rw [ofNat_toNat (by omega), ofNat_toNat (by omega)] at this
        exact this
      apply safe_assign
      refine Or.inr ⟨by simp [Regs.set, Expr.eval, truthy], fun it hit y w hy => ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hit
      have hall := doneCount_all (P := P) (σ := σ) (by rw [← hd, hdn'])
      have hst : (P.stH j .done y).isSome := by rw [stH_of_lt hj]; simp [Item.stH, hy]
      have ho := stH_owner hP hst
      refine union_some (union_some ?_)
      rw [union_or, ctlH_job F ho, jobH_owner ho, hall j hj, stH_of_lt hj]
      simpa [Item.stH] using hy
    · intro _
      exact safe_unlock M L hP.mlt ⟨k', d, e, σ, hk', hfr, hd, rfl⟩ tk d1 d2
        (fun rs3 => safe_assign (Or.inl ⟨by simp [Regs.set, Expr.eval, truthy], w, rfl⟩))

/-- **Each thread of the linked pool is safe**, for every mutex meeting the interface. -/
theorem thread_ok {t : Nat} (ht : t < P.K) :
    Csl.Safe (Inv M P) (Qt P t) (P.body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (P.cur t) 0) := by
  unfold Wp.body Qt
  by_cases h0 : t = 0
  · subst h0
    simp only [ite_true]
    apply safe_seq
    exact safe_conseq (fun rs h hp => by obtain ⟨w, rfl⟩ := hp; exact waitL_ok hP M L rs w)
      (worker_ok hP M L ht _ 0)
  · simp only [h0, ite_false]
    exact safe_conseq (fun _ _ _ => trivial) (worker_ok hP M L ht _ 0)

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
