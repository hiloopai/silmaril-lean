module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Heap

/-!
# Proofs: CSL rules for the pool's code

* `safe_ld`, `safe_st`: owned non-atomic 8-byte accesses at literal addresses;
* expression facts (`ev_lit`, `ltu_eval`, `eq_eval`, `add1_eval`);
* the **interface rules**, from `Mutex.Iface`'s fields only:
  * `safe_lock`: after `lock(l)` the thread also owns some `hR ⊨ R` and the token;
  * `safe_unlock`: `unlock(l)` hands `hR ⊨ R` and the token back;
  * `safe_crit`: a critical section `lock; body; unlock; cont` whose body re-splits the heap
    into a new `R`-heap and a new owned heap (the token is framed around the body).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool
open Silmaril.X86.Concurrency.Cir.Mutex (Iface)

/-! ## Expressions -/

theorem ev_lit {a : Nat} (h : a < 2 ^ 64) (rs : Regs) : ((Expr.lit a).eval rs).toNat = a := by
  simp [Expr.eval]; omega

theorem ofNat_toNat {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  simp; omega

theorem ltu_eval {rs : Regs} {r : Reg} {k n : Nat} (hr : rs r = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) (hn : n < 2 ^ 64) :
    truthy ((Expr.bin .ltu (.reg r) (.lit n)).eval rs) = decide (k < n) := by
  simp only [Expr.eval, BinOp.eval, hr, ofNat_toNat hk, ofNat_toNat hn, truthy]
  by_cases h : k < n <;> simp [h]

theorem eq_eval {rs : Regs} {r : Reg} {k j : Nat} (hr : rs r = BitVec.ofNat 64 k)
    (hk : k < 2 ^ 64) (hj : j < 2 ^ 64) :
    truthy ((Expr.bin .eq (.reg r) (.lit j)).eval rs) = decide (k = j) := by
  simp only [Expr.eval, BinOp.eval, hr, truthy]
  by_cases h : k = j
  · subst h; simp
  · have : BitVec.ofNat 64 k ≠ BitVec.ofNat 64 j := by
      intro e
      have := congrArg BitVec.toNat e
      rw [ofNat_toNat hk, ofNat_toNat hj] at this
      exact h this
    simp [this, h]

theorem and_eq_eval {rs : Regs} {r q : Reg} {a b : Nat}
    (h : truthy ((Expr.bin .and (.bin .eq (.reg r) (.lit a)) (.bin .eq (.reg q) (.lit b))).eval rs)
      = true) : rs r = BitVec.ofNat 64 a := by
  simp only [Expr.eval, BinOp.eval, truthy] at h
  by_cases e : rs r = BitVec.ofNat 64 a
  · exact e
  · simp [e] at h

theorem add1_eval {rs : Regs} {r : Reg} {k : Nat} (hr : rs r = BitVec.ofNat 64 k) :
    ((Expr.bin .add (.reg r) (.lit 1)).eval rs).toNat % 2 ^ 64 = (k + 1) % 2 ^ 64 := by
  simp only [Expr.eval, BinOp.eval, hr, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lit1_truthy (rs : Regs) : truthy ((Expr.lit 1).eval rs) = true := by
  simp [Expr.eval, truthy]

theorem lit0_truthy (rs : Regs) : truthy ((Expr.lit 0).eval rs) = false := by
  simp [Expr.eval, truthy]

/-! ## Owned accesses -/

theorem updH_wr {m : Mode} {fl : Flav} {a sz c : Nat} (h : Heap) :
    (Lab.wr m fl a sz c).updH h = fun y => if y = a then some c else h y := by
  funext y
  by_cases hy : y = a
  · subst hy; simp [Lab.updH, Lab.wval]
  · have : a ≠ y := Ne.symm hy
    simp [Lab.updH, Lab.wval, this, hy]

/-- `d := [a]` on an owned cell. -/
theorem safe_ld {I : HProp} {Q : Regs → HProp} {d : Reg} {a : Nat} {rs : Regs} {h : Heap}
    {v : Nat} (ha : a < 2 ^ 64) (hv : h a = some v) (hq : Q (rs.set d (BitVec.ofNat 64 v)) h) :
    Csl.Safe I Q (Wp.ldc d a) rs h :=
  safe_load_na (by rw [ev_lit ha]; exact hv) hq

/-- `[a] := e` on an owned cell, with the new heap given pointwise. -/
theorem safe_st {I : HProp} {Q : Regs → HProp} {a : Nat} {e : Expr} {rs : Regs} {h h' : Heap}
    {val : Nat} (ha : a < 2 ^ 64) (hdom : (h a).isSome)
    (hv : (e.eval rs).toNat % 2 ^ 64 = val)
    (heq : ∀ y, h' y = if y = a then some val else h y) (hq : Q rs h') :
    Csl.Safe I Q (Wp.stc a e) rs h := by
  apply safe_store_na (by rw [ev_lit ha]; exact hdom)
  have : h' = fun y => if y = a then some val else h y := funext heq
  rw [updH_wr, ev_lit ha, show 8 * 8 = 64 from rfl, hv, ← this]
  exact hq

/-! ## Rearranging disjoint unions -/

theorem union_swap {a b c : Heap} (d : Heap.Disjoint b c) :
    Heap.union (Heap.union a b) c = Heap.union (Heap.union a c) b := by
  rw [union_assoc, union_comm d, ← union_assoc]

/-! ## The interface rules -/

theorem rdi_lit {l : Nat} (hl : l < 2 ^ 64) (rs : Regs) :
    ((rs.set .rdi ((Expr.lit l).eval rs)) .rdi).toNat = l := by
  simp [Regs.set, Expr.eval]; omega

variable (M : Iface) (L : Nat) {l : Nat} (hl : l < 2 ^ 64) {R : HProp}
include hl

/-- **Lock**: after `lock(l)`, the thread owns its heap, some `hR ⊨ R` and a token. -/
theorem safe_lock {Q : Regs → HProp} {s : Stmt} {rs : Regs} {ho : Heap}
    (H : ∀ rs' hR htok, R hR → M.locked l htok → Heap.Disjoint hR htok →
      Heap.Disjoint (Heap.union hR htok) ho →
      Csl.Safe (M.inv l R ∗ hemp) Q s rs' (Heap.union (Heap.union hR htok) ho)) :
    Csl.Safe (M.inv l R ∗ hemp) Q (.seq (M.lock L (.lit l)) s) rs ho := by
  apply safe_seq
  apply safe_seq
  apply safe_assign
  have H0 := safe_frame (F := fun h => h = ho)
    (M.lock_spec l R hemp L _ (rdi_lit hl rs)) (disjoint_empty _) rfl
  rw [union_empty_left] at H0
  refine safe_conseq (fun rs' h hp => ?_) H0
  obtain ⟨h12, hF, d, rfl, hRL, rfl⟩ := sep_iff.mp hp
  obtain ⟨hR, htok, d12, rfl, r, t⟩ := sep_iff.mp hRL
  exact H rs' hR htok r t d12 d

/-- **Unlock**: `unlock(l)` hands `hR ⊨ R` and the token back. -/
theorem safe_unlock {Q : Regs → HProp} {cont : Stmt} {rs : Regs} {hR htok ho : Heap}
    (r : R hR) (t : M.locked l htok) (d1 : Heap.Disjoint hR htok)
    (d2 : Heap.Disjoint (Heap.union hR htok) ho)
    (H : ∀ rs', Csl.Safe (M.inv l R ∗ hemp) Q cont rs' ho) :
    Csl.Safe (M.inv l R ∗ hemp) Q (.seq (M.unlock L (.lit l)) cont) rs
      (Heap.union (Heap.union hR htok) ho) := by
  apply safe_seq
  apply safe_seq
  apply safe_assign
  have H0 := safe_frame (F := fun h => h = ho)
    (M.unlock_spec l R hemp L _ (Heap.union hR htok) (rdi_lit hl rs)
      (sep_iff.mpr ⟨hR, htok, d1, rfl, r, t⟩)) d2 rfl
  refine safe_conseq (fun rs' h hp => ?_) H0
  obtain ⟨h1, hF, -, rfl, e1, rfl⟩ := sep_iff.mp hp
  cases e1
  rw [union_empty_left]
  exact H rs'

/-- **A critical section** `lock(l); body; unlock(l); cont`. The body runs on `hR ∪ ho` for
any `hR ⊨ R` and must end with a new split `hR' ⊨ R`, `ho'` satisfying `G`; the token is
framed around it. -/
theorem safe_crit {Q : Regs → HProp} {body cont : Stmt} {rs : Regs} {ho : Heap}
    {G : Heap → Prop}
    (Hb : ∀ rs' hR, R hR → Heap.Disjoint hR ho →
      Csl.Safe (M.inv l R ∗ hemp)
        (fun _ h => ∃ hR' ho', Heap.Disjoint hR' ho' ∧ h = Heap.union hR' ho' ∧ R hR' ∧ G ho')
        body rs' (Heap.union hR ho))
    (Hc : ∀ rs' ho', G ho' → Csl.Safe (M.inv l R ∗ hemp) Q cont rs' ho') :
    Csl.Safe (M.inv l R ∗ hemp) Q
      (.seq (M.lock L (.lit l)) (.seq body (.seq (M.unlock L (.lit l)) cont))) rs ho := by
  apply safe_lock M L hl
  intro rs' hR htok r t d1 d2
  obtain ⟨dRo, dto⟩ := disjoint_union_left.mp d2
  have dRt : Heap.Disjoint (Heap.union hR ho) htok :=
    disjoint_union_left.mpr ⟨d1, disjoint_symm dto⟩
  rw [union_swap dto]
  apply safe_seq
  have H1 := safe_frame (F := fun h => h = htok) (Hb rs' hR r dRo) dRt rfl
  refine safe_conseq (fun rs2 h hp => ?_) H1
  obtain ⟨h1, h2, d12, rfl, ⟨hR', ho', d', rfl, r', g'⟩, rfl⟩ := sep_iff.mp hp
  obtain ⟨dR't, do't⟩ := disjoint_union_left.mp d12
  rw [union_swap do't]
  exact safe_unlock M L hl r' t dR't
    (disjoint_union_left.mpr ⟨d', disjoint_symm do't⟩) (fun rs3 => Hc rs3 ho' g')

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
