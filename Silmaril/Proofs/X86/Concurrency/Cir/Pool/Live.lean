module

public import Silmaril.X86.Concurrency.Cir.Progress.Thms
public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Cert

/-!
# Proofs: the linked pool cannot deadlock

The width map of a linked pool (`poolW`): the mutex's widths on its object, eight bytes on the
control cells and the run counters, nothing elsewhere (job inputs and outputs are read and
written only by blocks). Then:

* `pool_inv`: every thread body is thread-locally `Good` (`Progress.Inv`), from the leaves (all
  pool accesses are 8-byte accesses of literal addresses) and the mutex's `MutexLive` code;
* `mem_fits`: the linked pool's initial cells fit;
* `noDeadlock`: `Progress.stuck` with the certificate (`ginv`) gives `Task.poolNoDeadlock`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Concurrency.Cir.Mutex (Iface Client)
open Silmaril.X86.Concurrency.Cir.Progress (fits Good TReach MutexLive Agrees Exh lead
  inv_conseq inv_skip inv_seq inv_ite inv_loop inv_assign inv_load inv_store inv_block)
open Wp

/-- **The width map of the linked pool.** -/
def poolW (P : Wp) (M : Iface) (ML : MutexLive M) (a : Nat) : Option Nat :=
  if P.m ≤ a ∧ a < P.m + M.size then ML.wd P.m a
  else if a ∈ P.ctl ∨ ∃ it ∈ P.items, it.cnt = a then some 8 else none

/-- No register condition. -/
abbrev T : Regs → Prop := fun _ => True

theorem out_slot {P : Wp} {M : Iface} (hM : M.size ≤ P.slot) {a : Nat}
    (h : a < P.m ∨ P.m + P.slot ≤ a) : ¬ (P.m ≤ a ∧ a < P.m + M.size) := by
  omega

theorem fpB_mem {P : Wp} {j : Nat} (hj : j < P.n) {a : Nat} (h : a ∈ (P.items[j]'hj).fp) :
    P.fpB j a = true := by
  unfold Wp.fpB; rw [List.getElem?_eq_getElem hj]; simpa using h

theorem agrees {P : Wp} {M : Iface} (ML : MutexLive M) :
    Agrees (poolW P M ML) (ML.wd P.m) P.m M.size := by
  intro a h1 h2
  simp [poolW, h1, h2]

theorem toNat_lit {a : Nat} (h : a < 2 ^ 64) (rs : Regs) : ((Expr.lit a).eval rs).toNat = a := by
  simp only [Expr.eval, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem mem_ctl_qa {P : Wp} : P.qa ∈ P.ctl := by simp [Wp.ctl]
theorem mem_ctl_da {P : Wp} : P.da ∈ P.ctl := by simp [Wp.ctl]
theorem mem_ctl_ea {P : Wp} : P.ea ∈ P.ctl := by simp [Wp.ctl]
theorem mem_ctl_cur {P : Wp} {t : Nat} (ht : t < P.K) : P.cur t ∈ P.ctl :=
  List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr ht))

theorem mem0_ctl_zero {P : Wp} {a v : Nat} (h : (Heap.union (P.ctlH 0 0 0) P.cursH) a = some v) :
    v = 0 := by
  rw [union_or] at h
  cases e : P.ctlH 0 0 0 a with
  | some x =>
    rw [e] at h; cases h
    simp only [Wp.ctlH, union_or, single_apply] at e
    split_ifs at e <;> simp_all
  | none =>
    rw [e] at h
    simp only [Option.none_or, Wp.cursH] at h
    split at h <;> simp_all

section Code

variable {P : Wp} (hP : P.Ok) {M : Iface} (hM : M.size ≤ P.slot) (ML : MutexLive M)
include hP hM

theorem w_ctl {a : Nat} (ha : a ∈ P.ctl) : poolW P M ML a = some 8 := by
  simp [poolW, out_slot hM (hP.ctlLt a ha).2, ha]

theorem w_cnt {it : Item} (hit : it ∈ P.items) : poolW P M ML it.cnt = some 8 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hit
  have := (hP.fpLt j _ (fpB_cnt hj)).2
  simp only [poolW, out_slot hM this, ite_false]
  split
  · rfl
  · rename_i h; exact absurd (Or.inr ⟨_, hit, rfl⟩) h

theorem w_out {it : Item} (hit : it ∈ P.items) (htot : it.Total) {c : Nat × Nat}
    (hc : c ∈ it.job.outs) : poolW P M ML c.1 = none := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hit
  have hfp : P.fpB j c.1 = true :=
    fpB_mem hj (by simp only [Item.fp, List.mem_cons, List.mem_append, List.mem_map]
                   exact Or.inr (Or.inr ⟨c, hc, rfl⟩))
  have hown := hP.own j hj c.1 hfp
  simp only [poolW, out_slot hM (hP.fpLt j _ hfp).2, ite_false]
  split
  swap
  · rfl
  exfalso
  rename_i hcase
  rcases hcase with h | ⟨it', hit', e⟩
  · rw [hP.ctlOwn _ h] at hown; cases hown
  · obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hit'
    have := hP.own j' hj' _ (fpB_cnt hj')
    rw [e, hown] at this
    cases this
    exact htot.2 (List.mem_map.mpr ⟨c, hc, e.symm⟩)

/-! ## The code -/

omit hP hM in
theorem inv_ld {a : Nat} (ha : a < 2 ^ 64) (hw : poolW P M ML a = some 8) {d : Reg} :
    Progress.Inv (poolW P M ML) T (.load d .na 8 .wb (.lit a)) T :=
  inv_load (fun rs _ => ⟨8, by rw [toNat_lit ha]; exact hw, le_refl _⟩) fun _ _ _ => trivial

omit hP hM in
theorem inv_st {a : Nat} (ha : a < 2 ^ 64) (hw : poolW P M ML a = some 8) {v : Expr} :
    Progress.Inv (poolW P M ML) T (.store .na 8 .wb (.lit a) v) T :=
  inv_store (fun rs _ k hk => by rw [toNat_lit ha, hw] at hk; cases hk; exact le_refl _)
    fun _ _ => trivial

omit hP hM in
theorem inv_incr {a : Nat} (ha : a < 2 ^ 64) (hw : poolW P M ML a = some 8) :
    Progress.Inv (poolW P M ML) T (Item.incr a) T :=
  inv_seq (inv_ld ML ha hw) (inv_st ML ha hw)

omit hP hM in
theorem inv_asg {d : Reg} {e : Expr} : Progress.Inv (poolW P M ML) T (.assign d e) T :=
  inv_assign fun _ _ => trivial

omit hM in
theorem inv_lock (L : Nat) : Progress.Inv (poolW P M ML) T (M.lock L (.lit P.m)) T :=
  inv_seq (inv_assign (B := fun rs => (rs .rdi).toNat = P.m) fun rs _ => by
      have := hP.mlt; simp [Regs.set, Expr.eval]; omega)
    (ML.lock_inv P.m L _ (agrees ML))

omit hM in
theorem inv_unlock (L : Nat) : Progress.Inv (poolW P M ML) T (M.unlock L (.lit P.m)) T :=
  inv_seq (inv_assign (B := fun rs => (rs .rdi).toNat = P.m) fun rs _ => by
      have := hP.mlt; simp [Regs.set, Expr.eval]; omega)
    (ML.unlock_inv P.m L _ (agrees ML))

omit hM in
theorem inv_crit (L : Nat) {body cont : Stmt} (hb : Progress.Inv (poolW P M ML) T body T)
    (hc : Progress.Inv (poolW P M ML) T cont T) :
    Progress.Inv (poolW P M ML) T (P.crit (M.lock L) (M.unlock L) body cont) T :=
  inv_seq (inv_lock hP ML L) (inv_seq hb (inv_seq (inv_unlock hP ML L) hc))

theorem inv_ctl_ld {a : Nat} (ha : a ∈ P.ctl) {d : Reg} :
    Progress.Inv (poolW P M ML) T (.load d .na 8 .wb (.lit a)) T :=
  inv_ld ML (hP.ctlLt a ha).1 (w_ctl hP hM ML ha)

theorem inv_ctl_st {a : Nat} (ha : a ∈ P.ctl) {v : Expr} :
    Progress.Inv (poolW P M ML) T (.store .na 8 .wb (.lit a) v) T :=
  inv_st ML (hP.ctlLt a ha).1 (w_ctl hP hM ML ha)

theorem inv_ctl_incr {a : Nat} (ha : a ∈ P.ctl) : Progress.Inv (poolW P M ML) T (Item.incr a) T :=
  inv_incr ML (hP.ctlLt a ha).1 (w_ctl hP hM ML ha)

theorem inv_takeB {t : Nat} (ht : t < P.K) : Progress.Inv (poolW P M ML) T (P.takeB t) T :=
  inv_seq (inv_ctl_ld hP hM ML mem_ctl_qa)
    (inv_ite (inv_seq (inv_ctl_st hP hM ML mem_ctl_qa) (inv_ctl_st hP hM ML (mem_ctl_cur ht)))
      (inv_seq (inv_ctl_incr hP hM ML mem_ctl_ea) (inv_ctl_st hP hM ML (mem_ctl_cur ht))))

theorem inv_run (htot : ∀ it ∈ P.items, it.Total) {it : Item} (hit : it ∈ P.items) :
    Progress.Inv (poolW P M ML) T it.run T := by
  refine inv_seq (inv_block (B := T) ?_ ?_ fun _ _ _ => trivial) ?_
  · intro rs _ ivs hl
    refine ⟨[], it.job.fn ivs, rfl, (htot it hit).1 ivs hl, ?_⟩
    simp [Fj.Job.block]
  · intro c hc
    exact w_out hP hM ML hit (htot it hit) hc
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hit
    exact inv_incr ML (hP.fpLt j _ (fpB_cnt hj)).1 (w_cnt hP hM ML hit)

theorem inv_disp (htot : ∀ it ∈ P.items, it.Total) :
    ∀ (l : List Item), (∀ it ∈ l, it ∈ P.items) → ∀ j,
      Progress.Inv (poolW P M ML) T (disp l j) T
  | [], _, _ => inv_skip
  | it :: l, hl, j =>
    inv_ite (inv_run hP hM ML htot (hl it (List.mem_cons_self ..)))
      (inv_disp htot l (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (j + 1))

theorem inv_wbody (htot : ∀ it ∈ P.items, it.Total) (L : Nat) {t : Nat} (ht : t < P.K) :
    Progress.Inv (poolW P M ML) T (P.wbody (M.lock L) (M.unlock L) t) T :=
  inv_seq (inv_crit hP ML L (inv_takeB hP hM ML ht) inv_skip)
    (inv_seq (inv_ctl_ld hP hM ML (mem_ctl_cur ht))
      (inv_seq (inv_ite (inv_seq (inv_disp hP hM ML htot P.items (fun _ h => h) 0)
          (inv_crit hP ML L (inv_ctl_incr hP hM ML mem_ctl_da) inv_skip)) inv_skip)
        (inv_seq (inv_ctl_ld hP hM ML (mem_ctl_cur ht)) (inv_asg ML))))

theorem inv_worker (htot : ∀ it ∈ P.items, it.Total) (L : Nat) {t : Nat} (ht : t < P.K) :
    Progress.Inv (poolW P M ML) T (P.worker (M.lock L) (M.unlock L) t) T :=
  inv_seq (inv_asg ML) (inv_loop (inv_wbody hP hM ML htot L ht))

theorem inv_waitL (L : Nat) : Progress.Inv (poolW P M ML) T (P.waitL (M.lock L) (M.unlock L)) T :=
  inv_seq (inv_asg ML) (inv_loop (inv_seq (inv_lock hP ML L)
    (inv_seq (inv_ctl_ld hP hM ML mem_ctl_da) (inv_seq (inv_ctl_ld hP hM ML mem_ctl_ea)
      (inv_ite (inv_asg ML) (inv_seq (inv_unlock hP ML L) (inv_asg ML)))))))

/-- **Every thread of the linked pool is thread-locally `Good`.** -/
theorem pool_inv (htot : ∀ it ∈ P.items, it.Total) (L : Nat) {t : Nat} (ht : t < P.K) :
    Progress.Inv (poolW P M ML) T (P.body (M.lock L) (M.unlock L) t) T := by
  unfold Wp.body
  split
  · rename_i h; subst h
    exact inv_seq (inv_worker hP hM ML htot L ht) (inv_waitL hP hM ML L)
  · exact inv_worker hP hM ML htot L ht

/-! ## The initial cells -/

/-- **The linked pool's initial cells fit the width map.** -/
theorem mem_fits (L : Nat) :
    ∀ a v, (P.client.link M L).mem a = some v → fits (poolW P M ML) a v := by
  have F := ctlFacts hP
  intro a v h k hk
  have hmem : (P.client.link M L).mem =
      Heap.union P.mem0 (Heap.union (M.init P.m) Heap.empty) := rfl
  rw [hmem] at h
  cases e0 : P.mem0 a with
  | none =>
    rw [union_none e0, union_or] at h
    cases ei : M.init P.m a with
    | none => rw [ei] at h; cases h
    | some x =>
      rw [ei] at h; cases h
      have hd := M.init_dom P.m a (by simp [ei])
      simp only [poolW, hd, and_self, ↓reduceIte] at hk
      exact ML.init_fits P.m a _ ei k hk
  | some x =>
    rw [union_some e0] at h; cases h
    have hin : ¬ (P.m ≤ a ∧ a < P.m + M.size) := by
      intro hs
      rw [Wp.mem0, union_or, union_or] at e0
      cases e1 : P.ctlH 0 0 0 a with
      | some _ =>
        rcases ctlH_some (P := P) (k := 0) (d := 0) (e := 0) (a := a) (by simp [e1]) with
          h | h | h <;> subst h
        · exact out_slot hM (hP.ctlLt _ mem_ctl_qa).2 hs
        · exact out_slot hM (hP.ctlLt _ mem_ctl_da).2 hs
        · exact out_slot hM (hP.ctlLt _ mem_ctl_ea).2 hs
      | none =>
        rw [e1] at e0
        cases e2 : P.cursH a with
        | some _ =>
          have : (List.range P.K).any (fun t => P.cur t == a) = true := by
            simp only [Wp.cursH] at e2; split at e2 <;> simp_all
          obtain ⟨t, htm, et⟩ := List.any_eq_true.mp this
          have et := beq_iff_eq.mp et; subst et
          exact out_slot hM (hP.ctlLt _ (mem_ctl_cur (List.mem_range.mp htm))).2 hs
        | none =>
          rw [e2] at e0
          simp only [Option.none_or] at e0
          obtain ⟨j, hj⟩ := jobH_some (P := P) (σ := fun _ => .fresh) (a := a) (by simp [e0])
          exact out_slot hM (hP.fpLt j a (owner_spec hj).1).2 hs
    simp only [poolW, hin, ite_false] at hk
    split at hk
    · cases hk
      rename_i hc
      rw [Wp.mem0, union_or] at e0
      cases e1 : (Heap.union (P.ctlH 0 0 0) P.cursH) a with
      | some y =>
        rw [e1] at e0; cases e0
        rw [mem0_ctl_zero e1]; exact Nat.two_pow_pos _
      | none =>
        rw [e1] at e0
        simp only [Option.none_or] at e0
        obtain ⟨j, hj⟩ := jobH_some (P := P) (σ := fun _ => .fresh) (a := a) (by simp [e0])
        rcases hc with hc | ⟨it, hit, rfl⟩
        · rw [hP.ctlOwn _ hc] at hj; cases hj
        · obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hit
          have := hP.own j' hj' _ (fpB_cnt hj')
          rw [hj] at this; cases this
          rw [jobH_owner hj, stH_of_lt hj'] at e0
          simp only [Item.stH, Item.freshH_cnt] at e0
          cases e0; exact Nat.two_pow_pos _
    · cases hk

end Code

/-! ## No deadlock -/

theorem lead_eq : ∀ s, lead s = headS s
  | .seq s _ => by simp [lead, headS, lead_eq s]
  | .skip | .assign .. | .load .. | .store .. | .rmw .. | .fence .. | .futexWait ..
  | .futexWake .. | .spawn .. | .join .. | .local .. | .ite .. | .loop .. => rfl

/-- **No deadlock for every live mutex.** -/
theorem noDeadlock {M : Iface} (ML : MutexLive M) (P : Wp) : Task.poolNoDeadlock P M := by
  intro hP hM htot L model Cf hr hst
  have G := ginv hP M hM L
  have hg : ∀ t < P.client.N, ∀ p, TReach ((P.client.link M L).ts t) p →
      Good (poolW P M ML) p.1 p.2 := by
    intro t ht p hp
    have ht' : t < P.K := ht
    have : (P.client.link M L).ts t = (P.body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Client.link, Client.startWith, Wp.client, ht']
    rw [this] at hp
    exact (pool_inv hP hM ML htot L ht' _ trivial p hp).1
  rcases Progress.stuck G hg (mem_fits hP hM ML L) hr hst with h | ⟨t, ht, c, b, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, ht, c, b, by rw [← lead_eq]; exact h1, h2⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
