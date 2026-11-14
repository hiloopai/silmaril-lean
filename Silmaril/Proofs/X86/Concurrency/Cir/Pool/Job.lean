module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Rules

/-!
# Proofs: running one job

* `safe_run`: an item's code (`local job.block; [cnt] := [cnt] + 1`) on its fresh cells ends on
  its done cells. The block step is `lift_sequential`: its only obligation is the job's
  contract `outs = fn ins`, nothing about the job's code is re-proved.
* `safe_disp`: the dispatch on `r12 = k` runs job `k`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool

/-- The values a block reads, determined by the heap. -/
theorem ivs_eq : ∀ {cs : List (Nat × Nat)} {ivs : List Nat} {H : Heap},
    ivs.length = cs.length → (∀ c ∈ cellVals cs ivs, H c.1 = some c.2.2) →
    ivs = cs.map fun c => (H c.1).getD 0
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | c :: cs, v :: ivs, H, hl, hag => by
    simp only [cellVals, List.mem_cons, forall_eq_or_imp] at hag
    simp only [List.map_cons, hag.1, Option.getD_some, List.cons.injEq, true_and]
    exact ivs_eq (by simpa using hl) hag.2

namespace Item

theorem freshH_ins {it : Item} (hlen : it.arg.length = it.job.ins.length) :
    ∀ c ∈ it.job.ins, (it.freshH c.1).isSome := by
  intro c hc
  exact isSome_union_r (isSome_union_l (cellVals_cellsH_isSome (by omega) c hc))

theorem freshH_outs (it : Item) : ∀ c ∈ it.job.outs, (it.freshH c.1).isSome := by
  intro c hc
  exact isSome_union_r (isSome_union_r (cellVals_cellsH_isSome (by simp) c hc))

theorem blkH_cnt (it : Item) : (it.blkH it.cnt).isSome := by
  show ((it.blkLab.wval it.cnt).or (it.freshH it.cnt)).isSome
  rw [freshH_cnt]; cases it.blkLab.wval it.cnt <;> rfl

end Item

/-- **Running one job**: from its fresh cells, the item's code ends on its done cells. -/
theorem safe_run {I : HProp} {it : Item} (hlen : it.arg.length = it.job.ins.length)
    (hcnt : it.cnt < 2 ^ 64) (rs : Regs) :
    Csl.Safe I (fun _ h => h = it.doneH) it.run rs it.freshH := by
  apply safe_seq
  apply lift_sequential (Item.freshH_ins hlen) (Item.freshH_outs it)
  intro ivs rvs ovs hi hr ho hspec hag
  have hr0 : rvs = [] := List.eq_nil_of_length_eq_zero (by simpa [Fj.Job.block] using hr)
  subst hr0
  have hspec' : ovs = it.job.fn ivs := by simpa [Fj.Job.block] using hspec
  have hiv : ivs = it.ivals := ivs_eq (by simpa [Fj.Job.block] using hi) hag
  subst hiv hspec'
  show Csl.Safe I _ (Item.incr it.cnt) rs it.blkH
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (Item.blkH_cnt it)
  apply safe_seq
  apply safe_ld hcnt hw
  refine safe_st hcnt (by rw [hw]; rfl) (add1_eval (k := w) (by simp [Regs.set])) (h' := it.doneH)
    (fun y => ?_) rfl
  simp only [Item.doneH, hw, Option.getD_some]

/-- **Dispatch**: with `r12 = k`, the dispatch over `l` (indices from `j`) runs `l[k - j]`. -/
theorem safe_disp {I : HProp} {Q : Regs → HProp} {h : Heap} {k : Nat} (hk : k < 2 ^ 64) :
    ∀ (l : List Item) (j : Nat) (rs : Regs), rs .r12 = BitVec.ofNat 64 k → j ≤ k →
      k < j + l.length → j + l.length ≤ 2 ^ 64 →
      (∀ it, l[k - j]? = some it → Csl.Safe I Q it.run rs h) →
      Csl.Safe I Q (Wp.disp l j) rs h
  | [], j, _, _, h1, h2, _, _ => by simp at h2; omega
  | it :: l, j, rs, hr, h1, h2, h3, H => by
    simp only [Wp.disp]
    apply safe_ite
    · intro hc
      rw [eq_eval hr hk (by simp at h3; omega)] at hc
      have : k = j := by simpa using hc
      subst this
      exact H it (by simp)
    · intro hc
      rw [eq_eval hr hk (by simp at h3; omega)] at hc
      have hkj : k ≠ j := by simpa using hc
      refine safe_disp hk l (j + 1) rs hr (by omega) (by simp at h2; omega) (by simp at h3; omega)
        (fun it' e => H it' ?_)
      have : k - j = (k - (j + 1)) + 1 := by omega
      rw [this]; simpa using e

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
