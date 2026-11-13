module

public import Silmaril.Proofs.X86.Concurrency.Story.Pipe.Rules

/-!
# Proofs: the channel's `SafeR` specification

Under the channel invariant `Chan vs` alone (`Story.Pipe.Chan`):

* `send_chan`: `send k (vs[k])` from the producer's tokens `prodG k k` and no channel cells ends
  with `prodG (k + 1) (k + 1)` and no channel cells, from any flag;
* `recv_chan`: `recv k` from the consumer's tokens `consG k k` and its cells ends with
  `consG (k + 1) (k + 1)`, `out k = vs[k]` and the running sum advanced by `vs[k]`.

Each spin read is a shared step: when the value read is the literal it waits for, the thread's
tokens (`prod_agree`, `cons_agree`) and `Ok` leave exactly one channel state, in which the
payload is unclaimed, and the thread takes it (a claim). Each release store's obligation holds
in the one state its tokens and its claimed payload allow.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Silmaril.Proofs.X86.Concurrency.Story.Pipe

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Story.Pipe

/-- Pointwise Boolean identities between token predicates. -/
macro "gh_tac" : tactic => `(tactic| (intro f i hf; rcases f with _ | _ | _ | _ | _ | _ | f <;>
  simp <;> (try (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq])) <;> omega))

/-! ## What the tokens say -/

/-- **The producer's tokens pin `cP` and bound `s`.** -/
theorem prod_agree {c p s a cP cC : Nat} (d : Heap.Disjoint (prodG c p) (invG s a cP cC)) :
    cP = c ∧ s ≤ p := by
  simp only [prodG, invG, gh_disj] at d
  refine ⟨?_, ?_⟩
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact d 1 cP (by decide) (by simp; omega)
    · exact d 0 c (by decide) (by simp; omega)
  · by_contra hne
    exact d 2 p (by decide) (by simp; omega)

/-- **The consumer's tokens pin `cC` and bound `a`.** -/
theorem cons_agree {c a' s a cP cC : Nat} (d : Heap.Disjoint (consG c a') (invG s a cP cC)) :
    cC = c ∧ a ≤ a' := by
  simp only [consG, invG, gh_disj] at d
  refine ⟨?_, ?_⟩
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact d 4 cC (by decide) (by simp; omega)
    · exact d 3 c (by decide) (by simp; omega)
  · by_contra hne
    exact d 5 a' (by decide) (by simp; omega)

theorem prod_disj {c p s a cC : Nat} (hs : s ≤ p) :
    Heap.Disjoint (prodG c p) (invG s a c cC) := by
  simp only [prodG, invG, gh_disj]
  intro f i hf
  rcases f with _ | _ | _ | _ | _ | _ | f <;> simp; omega

theorem cons_disj {c a' s a cP : Nat} (ha : a ≤ a') :
    Heap.Disjoint (consG c a') (invG s a cP c) := by
  simp only [consG, invG, gh_disj]
  intro f i hf
  rcases f with _ | _ | _ | _ | _ | _ | f <;> simp; omega

/-- The token `P k`. -/
def pTok (k : Nat) : Heap := gh fun f i => f == 2 && i == k

/-- The token `A k`. -/
def aTok (k : Nat) : Heap := gh fun f i => f == 5 && i == k

/-! ## Channel cells -/

theorem ak_ne_sq : cack ≠ cseq := by decide
theorem dt_ne_sq : cdat ≠ cseq := by decide
theorem dt_ne_ak : cdat ≠ cack := by decide

theorem chanH_sq (vs : List Nat) (s a cP cC w : Nat) : chanH vs s a cP cC w cseq = some s := by
  simp [chanH]

theorem chanH_ak (vs : List Nat) (s a cP cC w : Nat) : chanH vs s a cP cC w cack = some a := by
  simp [chanH, ak_ne_sq]

theorem chanH_dt (vs : List Nat) (s a cP cC w : Nat) : chanH vs s a cP cC w cdat =
    (if s = a ∧ cP = s then some w
      else if s = a + 1 ∧ cC = a then some (vs.getD a 0) else none) := by
  simp [chanH, dt_ne_sq, dt_ne_ak]

theorem chanH_other (vs : List Nat) (s a cP cC w : Nat) {y : Nat} (h1 : y ≠ cseq) (h2 : y ≠ cack)
    (h3 : y ≠ cdat) : chanH vs s a cP cC w y = none := by
  simp [chanH, h1, h2, h3]

theorem ak_eval (rs : Regs) : ((Expr.lit cack).eval rs).toNat = cack := lit_eval _ (by decide) _
theorem sq_eval (rs : Regs) : ((Expr.lit cseq).eval rs).toNat = cseq := lit_eval _ (by decide) _
theorem dt_eval (rs : Regs) : ((Expr.lit cdat).eval rs).toNat = cdat := lit_eval _ (by decide) _

/-- The cells a load label touches. -/
theorem touches_rd {m : Mode} {fl : Flav} {a sz v y : Nat} :
    (Lab.rd m fl a sz v).Touches y ↔ y = a := by
  simp [Lab.Touches, Lab.reads, Lab.wval]

theorem okH_rd {H : Heap} {m : Mode} {fl : Flav} {a sz v : Nat} :
    (Lab.rd m fl a sz v).okH H ↔ H a = some v := by
  simp [Lab.okH, Lab.reads]

theorem updH_rd (H : Heap) (m : Mode) (fl : Flav) (a sz v : Nat) :
    (Lab.rd m fl a sz v).updH H = H := by
  funext x; rfl

theorem ofNat_ne {v k : Nat} (hv : v < 2 ^ 64) (hk : k < 2 ^ 64) (h : v ≠ k) :
    BitVec.ofNat 64 v ≠ BitVec.ofNat 64 k := by
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

/-! ## The producer's spin read -/

/-- **The producer's read of `cack`**, waiting for `k`: reading `k` claims the payload. -/
theorem ld_send {vs : List Nat} {k : Nat} {rs : Regs}
    {J : Bool → Regs → Heap → Heap → Prop}
    (h0 : ∀ v, v < 2 ^ 64 → v ≠ k → J false (rs.set .rax (BitVec.ofNat 64 v)) Heap.empty
      (prodG k k))
    (h1 : ∀ w, J false (rs.set .rax (BitVec.ofNat 64 k)) (Heap.single cdat w) (prodG (k + 1) k)) :
    SafeR (Chan vs) J false (.load .rax .acq 8 .wb (.lit cack)) rs Heap.empty (prodG k k) := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | load hv =>
    rename_i v
    rw [ak_eval]
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi _ dgI => ?_⟩)⟩
    obtain ⟨s, a, cP, cC, w, ok, rfl, rfl⟩ := hIi
    obtain ⟨hcP, hs⟩ := prod_agree dgI
    refine ⟨fun y hy => ?_, fun _ y e => by simp [Lab.wval] at e, fun hok => ?_⟩
    · rw [touches_rd] at hy; subst hy
      rw [union_empty_left, chanH_ak]; rfl
    · rw [okH_rd, union_empty_left, chanH_ak] at hok
      have hav : a = v := Option.some.inj hok
      rw [updH_rd, union_empty_left]
      by_cases hvk : v = k
      · obtain ⟨o1, o2, o3, o4⟩ := ok
        have e1 : a = k := hav.trans hvk
        have e2 : s = k := by omega
        have e3 : cC = k := by omega
        rw [e1, e2, e3, hcP, ← hvk]
        rw [hvk]
        refine ⟨Heap.single cdat w, chanH vs k k (k + 1) k w, prodG (k + 1) k,
          invG k k (k + 1) k, fun y => ?_, ?_, prod_disj (Nat.le_refl _), ?_,
          ⟨k, k, k + 1, k, w, ⟨by omega, by omega, by omega, by omega⟩, rfl, rfl⟩, h1 w,
          fun _ y e => by simp [Heap.empty] at e⟩
        · by_cases hy : y = cdat
          · subst hy; right; rw [chanH_dt]; simp
          · left; simp [single_apply, hy]
        · funext y
          rw [union_apply]
          by_cases hy : y = cdat
          · subst hy; rw [chanH_dt, chanH_dt]; simp [single_apply]
          · simp only [single_apply, hy, ite_false, Option.none_or]
            by_cases h1 : y = cseq
            · subst h1; rw [chanH_sq, chanH_sq]
            · by_cases h2 : y = cack
              · subst h2; rw [chanH_ak, chanH_ak]
              · rw [chanH_other _ _ _ _ _ _ h1 h2 hy, chanH_other _ _ _ _ _ _ h1 h2 hy]
        · simp only [prodG, invG, gh_union]
          apply gh_ext
          gh_tac
      · rw [hcP]
        refine ⟨Heap.empty, chanH vs s a k cC w, prodG k k, invG s a k cC,
          disjoint_empty _, union_empty_left _, prod_disj hs, rfl,
          ⟨s, a, k, cC, w, hcP ▸ ok, rfl, rfl⟩, ?_, fun _ y e => by simp [Heap.empty] at e⟩
        exact h0 v (by simpa using hv) hvk

/-! ## Registers and conditions -/

theorem set_set (rs : Regs) (r : Reg) (a b : Word) : (rs.set r a).set r b = rs.set r b := by
  funext q; simp only [Regs.set]; split <;> rfl

theorem set_get (rs : Regs) (r : Reg) (a : Word) : (rs.set r a) r = a := by simp [Regs.set]

theorem set_other (rs : Regs) {r q : Reg} (h : q ≠ r) (a : Word) : (rs.set r a) q = rs q := by
  simp [Regs.set, h]

theorem ne_cond (rs : Regs) (k : Nat) :
    truthy ((Expr.bin .ne (.reg .rax) (.lit k)).eval rs) =
      !(decide (rs .rax = BitVec.ofNat 64 k)) := by
  simp only [Expr.eval, BinOp.eval]
  by_cases h : rs .rax = BitVec.ofNat 64 k <;> simp [h, truthy]

/-- **A spin**, from a read lemma: the loop invariant is "not yet" (any value but `k` read, the
start resources) or "done" (`k` read, the claimed resources). -/
theorem safeR_spin {I : GProp} {Q : Bool → Regs → Heap → Heap → Prop} {B a k : Nat}
    (hk : k < 2 ^ 64) {rs : Regs} {h0 g0 : Heap} (D : Regs → Heap → Heap → Prop)
    (hld : ∀ rs', (∃ v, rs' = rs.set .rax (BitVec.ofNat 64 v)) ∨ rs' = rs →
      ∀ J : Bool → Regs → Heap → Heap → Prop,
      (∀ v, v < 2 ^ 64 → v ≠ k → J false (rs.set .rax (BitVec.ofNat 64 v)) h0 g0) →
      (∀ h g, D (rs.set .rax (BitVec.ofNat 64 k)) h g →
        J false (rs.set .rax (BitVec.ofNat 64 k)) h g) →
      SafeR I J false (.load .rax .acq 8 .wb (.lit a)) rs' h0 g0)
    (hQ : ∀ h g, D (rs.set .rax (BitVec.ofNat 64 k)) h g →
      Q false (rs.set .rax (BitVec.ofNat 64 k)) h g) :
    SafeR I Q false (spin B a k) rs h0 g0 := by
  let J : Bool → Regs → Heap → Heap → Prop := fun p rs' h g => p = false ∧
    ((∃ v, v < 2 ^ 64 ∧ v ≠ k ∧ rs' = rs.set .rax (BitVec.ofNat 64 v) ∧ h = h0 ∧ g = g0) ∨
      (rs' = rs.set .rax (BitVec.ofNat 64 k) ∧ D rs' h g))
  have hloop : ∀ p rs' h g, J p rs' h g →
      SafeR I Q p (.loop B (.bin .ne (.reg .rax) (.lit k)) (.load .rax .acq 8 .wb (.lit a)))
        rs' h g := by
    intro p rs' h g hJ
    refine safeR_loop (fun _ => J) (fun _ p rs' h g hJ hc => ?_) (fun _ p rs' h g hJ hc => ?_) hJ
    · obtain ⟨rfl, ⟨v, hv, hvk, rfl, rfl, rfl⟩ | ⟨rfl, hD⟩⟩ := hJ
      · rw [ne_cond, set_get] at hc
        simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
        exact absurd hc (ofNat_ne hv hk hvk)
      · exact hQ _ _ hD
    · obtain ⟨rfl, ⟨v, hv, hvk, rfl, rfl, rfl⟩ | ⟨rfl, hD⟩⟩ := hJ
      · refine hld _ (Or.inl ⟨v, rfl⟩) J (fun v' hv' hvk' => ?_) (fun h g hD => ?_)
        · exact ⟨rfl, Or.inl ⟨v', hv', hvk', rfl, rfl, rfl⟩⟩
        · exact ⟨rfl, Or.inr ⟨rfl, hD⟩⟩
      · rw [ne_cond, set_get] at hc; simp at hc
  unfold spin
  apply safeR_seq
  refine safeR_conseq (fun p rs' h g hJ => hloop p rs' h g hJ) ?_
  refine hld rs (Or.inr rfl) J (fun v hv hvk => ⟨rfl, Or.inl ⟨v, hv, hvk, rfl, rfl, rfl⟩⟩)
    (fun h g hD => ⟨rfl, Or.inr ⟨rfl, hD⟩⟩)

/-- **The producer's spin** until `cack = k`: it ends having claimed the payload. -/
theorem spin_send {vs : List Nat} {k B : Nat} (hk : k < 2 ^ 64) {rs : Regs}
    {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : ∀ w, Q false (rs.set .rax (BitVec.ofNat 64 k)) (Heap.single cdat w) (prodG (k + 1) k)) :
    SafeR (Chan vs) Q false (spin B cack k) rs Heap.empty (prodG k k) := by
  refine safeR_spin hk (fun _ h g => ∃ w, h = Heap.single cdat w ∧ g = prodG (k + 1) k)
    (fun rs' hrs J h0 h1 => ?_) (fun h g ⟨w, e1, e2⟩ => e1 ▸ e2 ▸ hQ w)
  refine ld_send (fun v hv hvk => ?_) (fun w => ?_)
  · rcases hrs with ⟨u, rfl⟩ | rfl
    · rw [set_set]; exact h0 v hv hvk
    · exact h0 v hv hvk
  · rcases hrs with ⟨u, rfl⟩ | rfl
    · rw [set_set]; exact h1 _ _ ⟨w, rfl, rfl⟩
    · exact h1 _ _ ⟨w, rfl, rfl⟩

/-! ## The producer's publication -/

theorem store_val (k : Nat) (hk : k < 2 ^ 64) (rs : Regs) :
    ((Expr.lit k).eval rs).toNat % 2 ^ (8 * 8) = k := by
  rw [lit_eval _ hk]; exact Nat.mod_eq_of_lt hk

theorem apply_st (H : Heap) (a v : Nat) (w : Bool) (y : Nat) :
    (Ent.st a v w).apply H y = if y = a then some v else H y := rfl

/-- **The producer's publication** of message `k` (payload `vs[k]`): the release store
`cseq := k + 1` gives the payload and `P k` to the channel. -/
theorem pub_send {vs : List Nat} {k w : Nat} (hk : k + 1 < 2 ^ 64) (hv : vs.getD k 0 < 2 ^ 64)
    {rs : Regs} {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : Q true rs Heap.empty (prodG (k + 1) (k + 1))) :
    SafeR (Chan vs) Q false (sendPub k (vs.getD k 0)) rs (Heap.single cdat w)
      (prodG (k + 1) k) := by
  unfold sendPub
  apply safeR_seq
  refine safeR_store_own (by rw [dt_eval]; simp [single_apply]) ?_
  rw [dt_eval, store_val _ hv]
  have hh : (fun x => if x = cdat then some (vs.getD k 0) else Heap.single cdat w x) =
      Heap.single cdat (vs.getD k 0) := by
    funext x; by_cases hx : x = cdat <;> simp [single_apply, hx]
  rw [hh]
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | store =>
    rw [sq_eval, store_val _ hk]
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨.rel, .wb, cseq, 8, k + 1, rfl, by decide, Heap.empty,
      Heap.single cdat (vs.getD k 0), prodG (k + 1) (k + 1), pTok k, disjoint_empty _,
      (union_empty_left _).symm, ?_, ?_, hQ, ?_⟩)⟩
    · simp only [prodG, pTok, gh_disj]
      intro f i hf; rcases f with _ | _ | _ | _ | _ | _ | f <;> simp; omega
    · simp only [prodG, pTok, gh_union]
      apply gh_ext
      gh_tac
    · intro hI gI hIi dH dG
      obtain ⟨s, a, cP, cC, w', ok, rfl, rfl⟩ := hIi
      obtain ⟨hcP, hs⟩ := prod_agree dG
      obtain ⟨o1, o2, o3, o4⟩ := ok
      have e2 : s = k := by omega
      have e1 : a = k := by omega
      have e3 : cC = k := by omega
      rw [e1, e2, e3, hcP]
      refine ⟨⟨cseq, k + 1, false, rfl, by rw [union_apply, chanH_sq]; simp [single_apply]⟩,
        k + 1, k, k + 1, k, w', ⟨by omega, by omega, by omega, by omega⟩, ?_, ?_⟩
      · funext y
        rw [apply_st, union_apply]
        by_cases h1 : y = cseq
        · subst h1; simp [chanH_sq]
        · simp only [h1, ite_false]
          by_cases hy : y = cdat
          · subst hy; rw [chanH_dt, chanH_dt]; simp [single_apply]
          · simp only [single_apply, hy, ite_false, Option.none_or]
            by_cases h2 : y = cack
            · subst h2; rw [chanH_ak, chanH_ak]
            · rw [chanH_other _ _ _ _ _ _ h1 h2 hy, chanH_other _ _ _ _ _ _ h1 h2 hy]
      · simp only [pTok, invG, gh_union]
        apply gh_ext
        gh_tac

/-- **`send k vs[k]`** under the channel invariant, from any flag. -/
theorem send_chan {vs : List Nat} {k B : Nat} {p : Bool} (hk : k + 1 < 2 ^ 64)
    (hv : vs.getD k 0 < 2 ^ 64) {rs : Regs} {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : ∀ rs', Q true rs' Heap.empty (prodG (k + 1) (k + 1))) :
    SafeR (Chan vs) Q p (send B k (vs.getD k 0)) rs Heap.empty (prodG k k) := by
  unfold send
  apply safeR_seq
  refine safeR_mfence ?_
  apply safeR_seq
  exact spin_send (by omega) (fun w => pub_send hk hv (hQ _))

/-! ## The consumer's spin read -/

/-- **The consumer's read of `cseq`**, waiting for `k + 1`: reading it claims the payload, which
is message `k`. -/
theorem ld_recv {vs : List Nat} {k : Nat} {rs : Regs} {J : Bool → Regs → Heap → Heap → Prop}
    (h0 : ∀ v, v < 2 ^ 64 → v ≠ k + 1 → J false (rs.set .rax (BitVec.ofNat 64 v)) Heap.empty
      (consG k k))
    (h1 : J false (rs.set .rax (BitVec.ofNat 64 (k + 1))) (Heap.single cdat (vs.getD k 0))
      (consG (k + 1) k)) :
    SafeR (Chan vs) J false (.load .rax .acq 8 .wb (.lit cseq)) rs Heap.empty (consG k k) := by
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | load hv =>
    rename_i v
    rw [sq_eval]
    refine ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, Or.inl rfl, fun hI gI hIi _ dgI => ?_⟩)⟩
    obtain ⟨s, a, cP, cC, w, ok, rfl, rfl⟩ := hIi
    obtain ⟨hcC, ha⟩ := cons_agree dgI
    refine ⟨fun y hy => ?_, fun _ y e => by simp [Lab.wval] at e, fun hok => ?_⟩
    · rw [touches_rd] at hy; subst hy
      rw [union_empty_left, chanH_sq]; rfl
    · rw [okH_rd, union_empty_left, chanH_sq] at hok
      have hsv : s = v := Option.some.inj hok
      rw [updH_rd, union_empty_left]
      by_cases hvk : v = k + 1
      · obtain ⟨o1, o2, o3, o4⟩ := ok
        have e2 : s = k + 1 := hsv.trans hvk
        have e1 : a = k := by omega
        have e3 : cP = k + 1 := by omega
        rw [e1, e2, e3, hcC, ← hvk]
        rw [hvk]
        refine ⟨Heap.single cdat (vs.getD k 0), chanH vs (k + 1) k (k + 1) (k + 1) w,
          consG (k + 1) k, invG (k + 1) k (k + 1) (k + 1), fun y => ?_, ?_,
          cons_disj (Nat.le_refl _), ?_,
          ⟨k + 1, k, k + 1, k + 1, w, ⟨by omega, by omega, by omega, by omega⟩, rfl, rfl⟩, h1,
          fun _ y e => by simp [Heap.empty] at e⟩
        · by_cases hy : y = cdat
          · subst hy; right; rw [chanH_dt]; simp
          · left; simp [single_apply, hy]
        · funext y
          rw [union_apply]
          by_cases hy : y = cdat
          · subst hy; rw [chanH_dt, chanH_dt]; simp [single_apply]
          · simp only [single_apply, hy, ite_false, Option.none_or]
            by_cases h1 : y = cseq
            · subst h1; rw [chanH_sq, chanH_sq]
            · by_cases h2 : y = cack
              · subst h2; rw [chanH_ak, chanH_ak]
              · rw [chanH_other _ _ _ _ _ _ h1 h2 hy, chanH_other _ _ _ _ _ _ h1 h2 hy]
        · simp only [consG, invG, gh_union]
          apply gh_ext
          gh_tac
      · rw [hcC]
        refine ⟨Heap.empty, chanH vs s a cP k w, consG k k, invG s a cP k,
          disjoint_empty _, union_empty_left _, cons_disj ha, rfl,
          ⟨s, a, cP, k, w, hcC ▸ ok, rfl, rfl⟩, ?_, fun _ y e => by simp [Heap.empty] at e⟩
        exact h0 v (by simpa using hv) hvk

/-- **The consumer's spin** until `cseq = k + 1`: it ends having claimed message `k`. -/
theorem spin_recv {vs : List Nat} {k B : Nat} (hk : k + 1 < 2 ^ 64) {rs : Regs}
    {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : Q false (rs.set .rax (BitVec.ofNat 64 (k + 1))) (Heap.single cdat (vs.getD k 0))
      (consG (k + 1) k)) :
    SafeR (Chan vs) Q false (spin B cseq (k + 1)) rs Heap.empty (consG k k) := by
  refine safeR_spin hk (fun _ h g => h = Heap.single cdat (vs.getD k 0) ∧ g = consG (k + 1) k)
    (fun rs' hrs J h0 h1 => ?_) (fun h g ⟨e1, e2⟩ => e1 ▸ e2 ▸ hQ)
  refine ld_recv (fun v hv hvk => ?_) ?_
  · rcases hrs with ⟨u, rfl⟩ | rfl
    · rw [set_set]; exact h0 v hv hvk
    · exact h0 v hv hvk
  · rcases hrs with ⟨u, rfl⟩ | rfl
    · rw [set_set]; exact h1 _ _ ⟨rfl, rfl⟩
    · exact h1 _ _ ⟨rfl, rfl⟩

/-! ## The consumer's take and acknowledgement -/

theorem out_far (k : Nat) : cdat < out k ∧ sm < out k ∧ cseq < out k ∧ cack < out k := by
  simp only [out, ob, cdat, sm, cseq, cack]; omega

/-- The consumer's cells after taking message `k` with value `x`: `out k = x` and `sm = S`. -/
def took (hO : Heap) (k x S : Nat) : Heap := fun y =>
  if y = sm then some S else if y = out k then some x else hO y

/-- **The consumer's take** of message `k` (value `x = vs[k]`, already claimed): `rcx := cdat`,
`out k := rcx`, `rbx := rbx + rcx`, `sm := rbx`, then the release store `cack := k + 1` gives the
payload and `A k` back to the channel. -/
theorem take_recv {vs : List Nat} {k : Nat} (hk : k + 1 < 2 ^ 64) (hx : vs.getD k 0 < 2 ^ 64)
    (hko : out k < 2 ^ 64) {rs : Regs} {hO : Heap} (hOd : hO cdat = none)
    (ho : (hO (out k)).isSome) (hs : (hO sm).isSome) {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : Q true ((rs.set .rcx (BitVec.ofNat 64 (vs.getD k 0))).set .rbx
        (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)))
      (took hO k (vs.getD k 0) (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)).toNat)
      (consG (k + 1) (k + 1))) :
    SafeR (Chan vs) Q false (recvTake k) rs (Heap.union (Heap.single cdat (vs.getD k 0)) hO)
      (consG (k + 1) k) := by
  obtain ⟨f1, f2, f3, f4⟩ := out_far k
  have hsm : sm < 2 ^ 64 := by decide
  set x := vs.getD k 0 with hxdef
  unfold recvTake
  apply safeR_seq
  refine safeR_load_own (v := x) (by rw [dt_eval, union_apply]; simp [single_apply]) ?_
  apply safeR_seq
  refine safeR_store_own (by rw [lit_eval _ hko, union_apply]; simp [single_apply,
    Nat.ne_of_gt f1, ho]) ?_
  apply safeR_seq
  refine safeR_assign ?_
  apply safeR_seq
  refine safeR_store_own (by rw [lit_eval _ hsm]; simp [Nat.ne_of_lt f2, union_apply,
    single_apply, show sm ≠ cdat by decide, hs, lit_eval _ hko]) ?_
  rw [lit_eval _ hko, lit_eval _ hsm]
  simp only [Expr.eval, BinOp.eval, set_get,
    set_other _ (show Silmaril.X86.Reg.rbx ≠ Silmaril.X86.Reg.rcx by decide)]
  refine safeR_atomic (by intro e; cases e) (fun s' rs' h => by cases h) ?_
  intro l s' rs' st
  cases st with
  | store =>
    rw [ak_eval, store_val _ hk]
    have hxm : x % 2 ^ (8 * 8) = x := Nat.mod_eq_of_lt hx
    have hSm : ∀ S : Word, S.toNat % 2 ^ (8 * 8) = S.toNat := fun S => Nat.mod_eq_of_lt S.isLt
    refine ⟨rfl, rfl, Or.inr (Or.inr ⟨.rel, .wb, cack, 8, k + 1, rfl, by decide,
      took hO k x (rs .rbx + BitVec.ofNat 64 x).toNat, Heap.single cdat x,
      consG (k + 1) (k + 1), aTok k, fun y => ?_, ?_, ?_, ?_, ?_, ?_⟩)⟩
    · by_cases hy : y = cdat
      · subst hy; left
        simp [took, Nat.ne_of_gt f1, Nat.ne_of_lt f1, show cdat ≠ sm by decide, hOd]
      · right; simp [single_apply, hy]
    · funext y
      simp only [took, union_apply, single_apply, set_get, BitVec.toNat_ofNat, hxm, hSm]
      by_cases h1 : y = sm
      · subst h1; simp
      · by_cases h2 : y = out k
        · subst h2; simp [h1, Nat.ne_of_gt f1]
        · by_cases h3 : y = cdat
          · subst h3; simp [h1, h2, hOd, Nat.ne_of_lt f1]
          · simp [h1, h2, h3]
    · simp only [consG, aTok, gh_disj]
      intro f i hf; rcases f with _ | _ | _ | _ | _ | _ | f <;> simp; omega
    · simp only [consG, aTok, gh_union]
      apply gh_ext
      gh_tac
    · simpa [hxdef] using hQ
    · intro hI gI hIi dH dG
      obtain ⟨s, a, cP, cC, w', ok, rfl, rfl⟩ := hIi
      obtain ⟨hcC, ha⟩ := cons_agree dG
      obtain ⟨o1, o2, o3, o4⟩ := ok
      have e1 : a = k := by omega
      have e2 : s = k + 1 := by omega
      have e3 : cP = k + 1 := by omega
      rw [e1, e2, e3, hcC]
      refine ⟨⟨cack, k + 1, false, rfl, by rw [union_apply, chanH_ak]; simp [single_apply]⟩,
        k + 1, k + 1, k + 1, k + 1, x, ⟨by omega, by omega, by omega, by omega⟩, ?_, ?_⟩
      · funext y
        rw [apply_st, union_apply]
        by_cases h2 : y = cack
        · subst h2; simp [chanH_ak]
        · simp only [h2, ite_false]
          by_cases hy : y = cdat
          · subst hy; rw [chanH_dt, chanH_dt]; simp [single_apply]
          · simp only [single_apply, hy, ite_false, Option.none_or]
            by_cases h1 : y = cseq
            · subst h1; rw [chanH_sq, chanH_sq]
            · rw [chanH_other _ _ _ _ _ _ h1 h2 hy, chanH_other _ _ _ _ _ _ h1 h2 hy]
      · simp only [aTok, invG, gh_union]
        apply gh_ext
        gh_tac

/-- **`recv k`** under the channel invariant, from any flag: it ends with `out k = vs[k]`, the
running sum advanced by `vs[k]` (in `rbx` and in `sm`), and the consumer's tokens moved on. -/
theorem recv_chan {vs : List Nat} {k B : Nat} {p : Bool} (hk : k + 1 < 2 ^ 64)
    (hx : vs.getD k 0 < 2 ^ 64) (hko : out k < 2 ^ 64) {rs : Regs} {hO : Heap}
    (hOd : hO cdat = none) (ho : (hO (out k)).isSome) (hs : (hO sm).isSome)
    {Q : Bool → Regs → Heap → Heap → Prop}
    (hQ : Q true (((rs.set .rax (BitVec.ofNat 64 (k + 1))).set .rcx
        (BitVec.ofNat 64 (vs.getD k 0))).set .rbx (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)))
      (took hO k (vs.getD k 0) (rs .rbx + BitVec.ofNat 64 (vs.getD k 0)).toNat)
      (consG (k + 1) (k + 1))) :
    SafeR (Chan vs) Q p (recv B k) rs hO (consG k k) := by
  unfold recv
  apply safeR_seq
  refine safeR_mfence ?_
  apply safeR_seq
  have hd : Heap.Disjoint (Heap.single cdat (vs.getD k 0)) hO := fun y => by
    by_cases hy : y = cdat
    · subst hy; right; exact hOd
    · left; simp [single_apply, hy]
  have H := safeR_frame (hF := hO) (spin_recv (B := B) (vs := vs) hk (rs := rs)
    (Q := fun p rs' h g => p = false ∧ rs' = rs.set .rax (BitVec.ofNat 64 (k + 1)) ∧
      h = Heap.single cdat (vs.getD k 0) ∧ g = consG (k + 1) k) ⟨rfl, rfl, rfl, rfl⟩)
    (disjoint_empty _)
  rw [union_empty_left] at H
  refine safeR_conseq (fun p rs' h g hp => ?_) H
  obtain ⟨h1, ⟨rfl, rfl, rfl, rfl⟩, -, rfl⟩ := hp
  refine take_recv hk hx hko hOd ho hs ?_
  rw [set_other _ (show Silmaril.X86.Reg.rbx ≠ Silmaril.X86.Reg.rax by decide)]
  exact hQ

end Silmaril.Proofs.X86.Concurrency.Story.Pipe
