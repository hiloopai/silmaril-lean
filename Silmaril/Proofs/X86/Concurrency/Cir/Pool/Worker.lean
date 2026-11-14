module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Job

/-!
# Proofs: the critical sections of the worker pool

On a heap `hR ∪ ho` with `hR ⊨ R`:

* `take_ok`: taking a job moves job `k`'s fresh cells from `R` to the worker (or, with the
  queue empty, counts an exit);
* `ret_ok`: returning job `k` moves its done cells back into `R`. That `σ k = taken` (the job
  is neither fresh nor already returned) is derived, not assumed: otherwise `R` and the worker
  would both hold job `k`'s counter cell.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool

namespace Wp

variable {P : Wp}

theorem ctlH_eq (k d e y : Nat) : P.ctlH k d e y =
    if y = P.qa then some k else if y = P.da then some d else if y = P.ea then some e
    else none := by
  simp only [Wp.ctlH, union_or, single_apply]
  split_ifs <;> simp

theorem stH_taken (k : Nat) : P.stH k .taken = Heap.empty := by
  unfold Wp.stH; split <;> rfl

theorem stH_of_lt {k : Nat} (hk : k < P.n) (s : St) : P.stH k s = (P.items[k]'hk).stH s := by
  unfold Wp.stH; rw [List.getElem?_eq_getElem hk]

theorem fpB_cnt {k : Nat} (hk : k < P.n) : P.fpB k (P.items[k]'hk).cnt = true := by
  unfold Wp.fpB; rw [List.getElem?_eq_getElem hk]; simp [Item.fp]

end Wp

open Wp

/-- What a worker owns after taking: job `k`'s fresh cells and `cur ↦ k`, or `cur ↦ n`. -/
def GT (P : Wp) (t : Nat) (ho : Heap) : Prop :=
  (∃ k < P.n, ho = Heap.union (P.stH k .fresh) (Heap.single (P.cur t) k)) ∨
    ho = Heap.single (P.cur t) P.n

/-- What a worker owns after returning: its private cell. -/
def GR (P : Wp) (t : Nat) (ho : Heap) : Prop := ∃ v, ho = Heap.single (P.cur t) v

variable {P : Wp} (hP : P.Ok) {I : HProp}
include hP

/-- **Taking a job.** -/
theorem take_ok {t : Nat} (ht : t < P.K) {v : Nat} (rs : Regs) {hR : Heap} (r : P.R hR) :
    Csl.Safe I (fun _ h => ∃ hR' ho', Heap.Disjoint hR' ho' ∧ h = Heap.union hR' ho' ∧
      P.R hR' ∧ GT P t ho') (P.takeB t) rs (Heap.union hR (Heap.single (P.cur t) v)) := by
  obtain ⟨k, d, e, σ, hk, hfr, hd, rfl⟩ := r
  have F := ctlFacts hP
  have hn := hP.nlt
  have cq := F.cq t ht
  have cd := F.cd t ht
  have ce := F.ce t ht
  have oc := F.oc t ht
  unfold Wp.takeB
  apply safe_seq
  apply safe_ld F.lq (v := k)
    (by rw [union_or, union_or, ctlH_eq]; simp)
  apply safe_ite
  · intro hc
    rw [ltu_eval (k := k) (by simp [Regs.set]) (by omega) (by omega)] at hc
    have hkn : k < P.n := by simpa using hc
    have hσ : σ k = .fresh := (hfr k hkn).mpr (Nat.le_refl _)
    apply safe_seq
    refine safe_st F.lq (by rw [union_or, union_or, ctlH_eq]; simp) (val := k + 1)
      (by rw [add1_eval (k := k) (by simp [Regs.set])]; omega) (fun _ => rfl) ?_
    refine safe_st (F.lc t ht)
      (by simp only [cq, ite_false]; exact isSome_union_r (by simp [single_apply]))
      (val := k) (by simp [Expr.eval, Regs.set]; omega) (fun _ => rfl) ?_
    refine ⟨Heap.union (P.ctlH (k + 1) d e) (P.jobH (upd σ k .taken)),
      Heap.union (P.stH k .fresh) (Heap.single (P.cur t) k), ?_, ?_, ?_, Or.inl ⟨k, hkn, rfl⟩⟩
    · apply disjoint_of
      intro y hy
      rw [union_or] at hy
      rw [union_or, single_apply]
      cases e1 : P.ctlH (k + 1) d e y with
      | some w =>
        have hy' := ctlH_some (P := P) (k := k + 1) (d := d) (e := e) (a := y) (by simp [e1])
        rcases hy' with rfl | rfl | rfl
        · simp [stH_none hP (s := .fresh) (j := k) (a := P.qa) (by simp [F.oq]), Ne.symm cq]
        · simp [stH_none hP (s := .fresh) (j := k) (a := P.da) (by simp [F.od]), Ne.symm cd]
        · simp [stH_none hP (s := .fresh) (j := k) (a := P.ea) (by simp [F.oe]), Ne.symm ce]
      | none =>
        rw [e1] at hy
        simp only [Option.none_or] at hy
        obtain ⟨j, hj⟩ := jobH_some hy
        rw [jobH_upd, hj] at hy
        have hyc := (owner_ne_ctl F hj).2.2.2 t ht
        by_cases hjk : j = k
        · subst hjk; simp [stH_taken, Heap.empty] at hy
        · have : P.owner y ≠ some k := by rw [hj]; simpa using hjk
          simp [stH_none hP this, hyc]
    · funext y
      simp only [union_or, single_apply, jobH_upd]
      by_cases h1 : y = P.cur t
      · subst h1
        simp [ctlH_eq, cq, cd, ce, oc, jobH_none oc, stH_none hP (s := .fresh) (j := k)
          (a := P.cur t) (by simp [oc])]
      by_cases h2 : y = P.qa
      · subst h2; simp [ctlH_eq, h1]
      simp only [h1, h2, ite_false]
      cases ho : P.owner y with
      | none =>
        simp [jobH_none ho, stH_none hP (s := .fresh) (j := k) (a := y) (by simp [ho]), ctlH_eq,
          h2]
      | some j =>
        have hne := owner_ne_ctl F ho
        rw [ctlH_other hne.1 hne.2.1 hne.2.2.1, ctlH_other hne.1 hne.2.1 hne.2.2.1,
          jobH_owner ho]
        by_cases hjk : j = k
        · subst hjk; simp [hσ, stH_taken, Heap.empty]
        · have : P.owner y ≠ some k := by rw [ho]; simpa using hjk
          simp [hjk, stH_none hP this]
    · refine ⟨k + 1, d, e, upd σ k .taken, by omega, fun j hj => ?_, ?_, rfl⟩
      · by_cases hjk : j = k
        · subst hjk; simp [upd]
        · simp only [upd, hjk, ite_false]
          rw [hfr j hj]; omega
      · rw [doneCount_upd_taken hkn (by simp [hσ])]; exact hd
  · intro hc
    rw [ltu_eval (k := k) (by simp [Regs.set]) (by omega) (by omega)] at hc
    have hkn : k = P.n := by simp at hc; omega
    subst hkn
    apply safe_seq
    unfold Item.incr
    apply safe_seq
    apply safe_ld F.le (v := e)
      (by rw [union_or, union_or, ctlH_eq]; simp [Ne.symm F.qe, Ne.symm F.de])
    refine safe_st F.le
      (by rw [union_or, union_or, ctlH_eq]; simp [Ne.symm F.qe, Ne.symm F.de])
      (add1_eval (k := e) (by simp [Regs.set])) (fun _ => rfl) ?_
    refine safe_st (F.lc t ht)
      (by simp only [ce, ite_false]; exact isSome_union_r (by simp [single_apply]))
      (val := P.n) (by simp [Expr.eval]; omega) (fun _ => rfl) ?_
    refine ⟨Heap.union (P.ctlH P.n d ((e + 1) % 2 ^ 64)) (P.jobH σ),
      Heap.single (P.cur t) P.n, ?_, ?_, ⟨P.n, d, _, σ, hk, hfr, hd, rfl⟩, Or.inr rfl⟩
    · apply disjoint_of
      intro y hy
      rw [union_or] at hy
      rw [single_apply]
      cases e1 : P.ctlH P.n d ((e + 1) % 2 ^ 64) y with
      | some w =>
        have hy' := ctlH_some (P := P) (k := P.n) (d := d) (e := (e + 1) % 2 ^ 64) (a := y)
          (by rw [e1]; rfl)
        rcases hy' with rfl | rfl | rfl <;> simp [Ne.symm cq, Ne.symm cd, Ne.symm ce]
      | none =>
        rw [e1] at hy
        simp only [Option.none_or] at hy
        obtain ⟨j, hj⟩ := jobH_some hy
        simp [(owner_ne_ctl F hj).2.2.2 t ht]
    · funext y
      simp only [union_or, single_apply]
      by_cases h1 : y = P.cur t
      · subst h1; simp [ctlH_eq, cq, cd, ce, jobH_none oc]
      by_cases h2 : y = P.ea
      · subst h2; simp [ctlH_eq, h1, Ne.symm F.qe, Ne.symm F.de]
      simp only [h1, h2, ite_false, ctlH_eq]

/-- **Returning job `k`.** -/
theorem ret_ok {t : Nat} (ht : t < P.K) {k : Nat} (hk : k < P.n) (rs : Regs) {hR : Heap}
    (r : P.R hR) (dis : Heap.Disjoint hR
      (Heap.union (P.stH k .done) (Heap.single (P.cur t) k))) :
    Csl.Safe I (fun _ h => ∃ hR' ho', Heap.Disjoint hR' ho' ∧ h = Heap.union hR' ho' ∧
      P.R hR' ∧ GR P t ho') P.retB rs
      (Heap.union hR (Heap.union (P.stH k .done) (Heap.single (P.cur t) k))) := by
  obtain ⟨k', d, e, σ, hk', hfr, hd, rfl⟩ := r
  have F := ctlFacts hP
  have hn := hP.nlt
  have cq := F.cq t ht
  have cd := F.cd t ht
  have ce := F.ce t ht
  have oc := F.oc t ht
  -- job `k` is taken: otherwise its counter cell is in both heaps
  have hσ : σ k = .taken := by
    have hown := hP.own k hk _ (fpB_cnt hk)
    have h2 : ((Heap.union (P.stH k .done) (Heap.single (P.cur t) k))
        (P.items[k]'hk).cnt).isSome := by
      apply isSome_union_l; rw [stH_of_lt hk]; exact Item.doneH_cnt _
    cases hs : σ k with
    | taken => rfl
    | fresh =>
      exfalso
      refine disjoint_some dis ?_ h2
      apply isSome_union_r; rw [jobH_owner hown, hs, stH_of_lt hk]
      simp [Item.stH, Item.freshH_cnt]
    | done =>
      exfalso
      refine disjoint_some dis ?_ h2
      apply isSome_union_r; rw [jobH_owner hown, hs, stH_of_lt hk]
      exact Item.doneH_cnt _
  have hlt : d + 1 ≤ P.n := by
    have := doneCount_le (P := P) (upd σ k .done)
    rw [doneCount_upd_done hk (by simp [hσ])] at this; omega
  unfold Wp.retB Item.incr
  apply safe_seq
  apply safe_ld F.ld (v := d) (by rw [union_or, union_or, ctlH_eq]; simp [Ne.symm F.qd])
  refine safe_st F.ld (by rw [union_or, union_or, ctlH_eq]; simp [Ne.symm F.qd])
    (val := d + 1) (by rw [add1_eval (k := d) (by simp [Regs.set])]; omega) (fun _ => rfl) ?_
  refine ⟨Heap.union (P.ctlH k' (d + 1) e) (P.jobH (upd σ k .done)),
    Heap.single (P.cur t) k, ?_, ?_, ?_, ⟨k, rfl⟩⟩
  · apply disjoint_of
    intro y hy
    rw [union_or] at hy
    rw [single_apply]
    cases e1 : P.ctlH k' (d + 1) e y with
    | some w =>
      have hy' := ctlH_some (P := P) (k := k') (d := d + 1) (e := e) (a := y) (by simp [e1])
      rcases hy' with rfl | rfl | rfl <;> simp [Ne.symm cq, Ne.symm cd, Ne.symm ce]
    | none =>
      rw [e1] at hy
      simp only [Option.none_or] at hy
      obtain ⟨j, hj⟩ := jobH_some hy
      simp [(owner_ne_ctl F hj).2.2.2 t ht]
  · funext y
    simp only [union_or, single_apply, jobH_upd]
    by_cases h2 : y = P.da
    · subst h2; simp [ctlH_eq, Ne.symm F.qd]
    by_cases h1 : y = P.cur t
    · subst h1
      simp [ctlH_eq, cq, cd, ce, oc, jobH_none oc, stH_none hP (s := .done) (j := k)
        (a := P.cur t) (by simp [oc])]
    simp only [h1, h2, ite_false]
    cases ho : P.owner y with
    | none =>
      simp [jobH_none ho, stH_none hP (s := .done) (j := k) (a := y) (by simp [ho]), ctlH_eq, h2]
    | some j =>
      have hne := owner_ne_ctl F ho
      rw [ctlH_other hne.1 hne.2.1 hne.2.2.1, ctlH_other hne.1 hne.2.1 hne.2.2.1,
        jobH_owner ho]
      by_cases hjk : j = k
      · subst hjk; simp [hσ, stH_taken, Heap.empty]
      · have : P.owner y ≠ some k := by rw [ho]; simpa using hjk
        simp [hjk, stH_none hP this]
  · refine ⟨k', d + 1, e, upd σ k .done, hk', fun j hj => ?_, ?_, rfl⟩
    · by_cases hjk : j = k
      · subst hjk
        have := hfr j hj
        simp only [upd, ite_true]
        rw [hσ] at this
        simp at this ⊢; omega
      · simp only [upd, hjk, ite_false]; exact hfr j hj
    · rw [doneCount_upd_done hk (by simp [hσ]), hd]

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
