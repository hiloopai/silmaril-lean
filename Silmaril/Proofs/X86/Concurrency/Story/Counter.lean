module

public import Silmaril.X86.Concurrency.Story.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Thms
public import Silmaril.X86.Concurrency.Cir.Csl.Rel.Thms
public import Mathlib.Data.Finset.Card

/-!
# Proofs: the counter client, proved once against the mutex interface

`Story.Counter.client N` (`N` threads, each `lock(m); x := x + 1; unlock(m)`) is proved against
**every** mutex meeting the interface `Mutex.Iface` (the logic; `counter_ginv`) and against
every mutex meeting the ghost-aware interface `Mutex.IfaceG` (the release logic `SafeR`;
`counter_ginvG`). The proofs use only the interfaces' fields: `lock_spec`, `unlock_spec`,
`init_inv`, `init_dom` (and, for `IfaceG`, the ghost fields `ready_thr`, `gthr_disj`,
`ginit_disj`).

How the count is obtained without ghost state. The lock's resource `R N` holds the counter and
**token cells** that no instruction accesses: when `S` is the set of threads that have
incremented, it owns `x ↦ |S|` (while `|S| < N`), the permits of `S`, and the receipts
`[|S|, N)`. A thread starts owning its permit. In the critical section it reads `v = |S|`
(`v < N`, since its own permit is not in `S`), writes `v + 1`, gives its permit to `R` and takes
receipt `v`; the thread that writes `N` also takes the counter out of `R`. At a finished state
the `N` postconditions hold on pairwise disjoint heaps, so the `N` receipts are distinct numbers
below `N`, one of them is `N - 1`, and its owner holds `x ↦ N`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Story

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Csl.Rel
open Silmaril.X86.Concurrency.Cir.Mutex
open Silmaril.X86.Concurrency.Story.Counter

/-! ## Heaps -/

theorem union_apply (h₁ h₂ : Heap) (a : Nat) : Heap.union h₁ h₂ a = (h₁ a).or (h₂ a) := by
  simp only [Heap.union, Silmaril.X86.Sep.BI.SepAlg.pmapUnion]; cases h₁ a <;> rfl

theorem single_apply (a v y : Nat) : Heap.single a v y = if y = a then some v else none := rfl

theorem empty_apply (y : Nat) : Heap.empty y = none := rfl

theorem union_eq_none {h₁ h₂ : Heap} {a : Nat} :
    Heap.union h₁ h₂ a = none ↔ h₁ a = none ∧ h₂ a = none := by
  rw [union_apply]; cases h₁ a <;> simp

theorem union_empty_left (h : Heap) : Heap.union Heap.empty h = h := by
  funext y; simp [union_apply, empty_apply]

theorem union_empty_right (h : Heap) : Heap.union h Heap.empty = h := by
  funext y; cases e : h y <;> simp [union_apply, e, empty_apply]

theorem disjoint_empty (h : Heap) : Heap.Disjoint Heap.empty h := fun _ => Or.inl rfl

theorem disjoint_empty_right (h : Heap) : Heap.Disjoint h Heap.empty := fun _ => Or.inr rfl

theorem ite_none {c : Prop} [Decidable c] {a : Option Nat} (h : ¬ c) :
    (if c then a else none) = none := by simp [h]

theorem ite_some {c : Prop} [Decidable c] {a b : Option Nat} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem updH_wr {m : Mode} {fl : Flav} {a sz c : Nat} (h : Heap) :
    (Lab.wr m fl a sz c).updH h = fun y => if y = a then some c else h y := by
  funext y
  by_cases hy : y = a
  · subst hy; simp [Lab.updH, Lab.wval]
  · have : a ≠ y := Ne.symm hy
    simp [Lab.updH, Lab.wval, this, hy]

/-! ## Token cells -/

/-- The permits of `S`. -/
def pH (S : Finset Nat) : Heap := fun a =>
  if tb ≤ a ∧ (a - tb) % 16 = 0 ∧ (a - tb) / 16 ∈ S then some 0 else none

/-- The receipts numbered in `[lo, N)`. -/
def rH (lo N : Nat) : Heap := fun a =>
  if tb ≤ a ∧ (a - tb) % 16 = 8 ∧ lo ≤ (a - tb) / 16 ∧ (a - tb) / 16 < N then some 0 else none

/-- The counter cell holding `v`, if `b`. -/
def xH (b : Bool) (v : Nat) : Heap := if b then Heap.single x v else Heap.empty

/-- **The resource's heap** after the threads of `S` have incremented. -/
def cH (N : Nat) (S : Finset Nat) : Heap :=
  Heap.union (xH (decide (S.card < N)) S.card) (Heap.union (pH S) (rH S.card N))

/-- **The resource the mutex protects.** -/
def R (N : Nat) : HProp := fun h => ∃ S : Finset Nat, S ⊆ Finset.range N ∧ h = cH N S

/-- What thread `t` ends with: a receipt `k < N`, and the counter `x ↦ N` if `k = N - 1`. -/
def post (N : Nat) (_t : Nat) : Regs → HProp := fun _ h =>
  ∃ k < N, h = Heap.union (Heap.single (receipt k) 0) (xH (decide (k + 1 = N)) N)

theorem x_lt_tb : x < tb := by decide

@[simp] theorem pH_x (S : Finset Nat) : pH S x = none := by
  simp only [pH]; rw [ite_none]; have := x_lt_tb; omega

@[simp] theorem rH_x (lo N : Nat) : rH lo N x = none := by
  simp only [rH]; rw [ite_none]; have := x_lt_tb; omega

@[simp] theorem pH_permit (S : Finset Nat) (k : Nat) :
    pH S (permit k) = if k ∈ S then some 0 else none := by
  have h1 : tb ≤ permit k := by simp [permit]
  have h2 : (permit k - tb) % 16 = 0 := by simp only [permit]; omega
  have h3 : (permit k - tb) / 16 = k := by simp only [permit]; omega
  simp [pH, h1, h2, h3]

@[simp] theorem pH_receipt (S : Finset Nat) (k : Nat) : pH S (receipt k) = none := by
  simp only [pH]; rw [ite_none]; simp only [receipt]; omega

@[simp] theorem rH_permit (lo N k : Nat) : rH lo N (permit k) = none := by
  simp only [rH]; rw [ite_none]; simp only [permit]; omega

@[simp] theorem rH_receipt (lo N k : Nat) :
    rH lo N (receipt k) = if lo ≤ k ∧ k < N then some 0 else none := by
  have h1 : tb ≤ receipt k := by simp only [receipt]; omega
  have h2 : (receipt k - tb) % 16 = 8 := by simp only [receipt]; omega
  have h3 : (receipt k - tb) / 16 = k := by simp only [receipt]; omega
  simp [rH, h1, h2, h3]

@[simp] theorem x_ne_permit (k : Nat) : (x = permit k) = False := by
  apply propext; constructor
  · intro h; have := x_lt_tb; simp only [permit] at h; omega
  · intro h; cases h

@[simp] theorem x_ne_receipt (k : Nat) : (x = receipt k) = False := by
  apply propext; constructor
  · intro h; have := x_lt_tb; simp only [receipt] at h; omega
  · intro h; cases h

@[simp] theorem permit_ne_x (k : Nat) : (permit k = x) = False := by
  apply propext; constructor
  · intro h; have := x_lt_tb; simp only [permit] at h; omega
  · intro h; cases h

@[simp] theorem receipt_ne_x (k : Nat) : (receipt k = x) = False := by
  apply propext; constructor
  · intro h; have := x_lt_tb; simp only [receipt] at h; omega
  · intro h; cases h

@[simp] theorem permit_ne_receipt (j k : Nat) : (permit j = receipt k) = False := by
  apply propext; constructor
  · intro h; simp only [permit, receipt] at h; omega
  · intro h; cases h

@[simp] theorem receipt_ne_permit (j k : Nat) : (receipt j = permit k) = False := by
  apply propext; constructor
  · intro h; simp only [permit, receipt] at h; omega
  · intro h; cases h

@[simp] theorem permit_inj (j k : Nat) : (permit j = permit k) = (j = k) := by
  apply propext; constructor
  · intro h; simp only [permit] at h; omega
  · intro h; rw [h]

@[simp] theorem receipt_inj (j k : Nat) : (receipt j = receipt k) = (j = k) := by
  apply propext; constructor
  · intro h; simp only [receipt] at h; omega
  · intro h; rw [h]

/-- Every address is the counter, a permit, a receipt, or none of the token cells. -/
theorem classify (y : Nat) :
    y = x ∨ (∃ k, y = permit k) ∨ (∃ k, y = receipt k) ∨
      (y ≠ x ∧ ∀ S lo N, pH S y = none ∧ rH lo N y = none) := by
  by_cases hx : y = x
  · exact .inl hx
  by_cases hp : tb ≤ y ∧ (y - tb) % 16 = 0
  · exact .inr (.inl ⟨(y - tb) / 16, by simp only [permit]; omega⟩)
  by_cases hr : tb ≤ y ∧ (y - tb) % 16 = 8
  · exact .inr (.inr (.inl ⟨(y - tb) / 16, by simp only [receipt]; omega⟩))
  refine .inr (.inr (.inr ⟨hx, fun S lo N => ⟨?_, ?_⟩⟩))
  · simp only [pH]; rw [ite_none]; omega
  · simp only [rH]; rw [ite_none]; omega

@[simp] theorem xH_x (b : Bool) (v : Nat) : xH b v x = if b then some v else none := by
  cases b <;> simp [xH, single_apply, empty_apply]

@[simp] theorem xH_permit (b : Bool) (v k : Nat) : xH b v (permit k) = none := by
  cases b <;> simp [xH, single_apply, empty_apply]

@[simp] theorem xH_receipt (b : Bool) (v k : Nat) : xH b v (receipt k) = none := by
  cases b <;> simp [xH, single_apply, empty_apply]

theorem xH_other {y : Nat} (hy : y ≠ x) (b : Bool) (v : Nat) : xH b v y = none := by
  cases b <;> simp [xH, single_apply, empty_apply, hy]

/-! ## The counting argument -/

/-- **`N` disjoint postconditions put the counter at `N`.** -/
theorem count {N : Nat} (hN : 0 < N) {hs : Nat → Heap}
    (hq : ∀ t < N, ∃ k < N, hs t = Heap.union (Heap.single (receipt k) 0) (xH (decide (k + 1 = N)) N))
    (hd : ∀ t u, t ≠ u → Heap.Disjoint (hs t) (hs u)) : ∃ t < N, hs t x = some N := by
  classical
  let k : Nat → Nat := fun t => if h : t < N then Classical.choose (hq t h) else 0
  have hk : ∀ t (ht : t < N), k t < N ∧
      hs t = Heap.union (Heap.single (receipt (k t)) 0) (xH (decide (k t + 1 = N)) N) := by
    intro t ht
    have := Classical.choose_spec (hq t ht)
    simp only [k, ht, ↓reduceDIte]
    exact this
  have hinj : Set.InjOn k (Finset.range N) := by
    intro t ht u hu e
    simp only [Finset.coe_range, Set.mem_Iio] at ht hu
    by_contra hne
    rcases hd t u hne (receipt (k t)) with h | h
    · rw [(hk t ht).2] at h; simp [union_apply, single_apply] at h
    · rw [(hk u hu).2, e] at h; simp [union_apply, single_apply] at h
  have himg : (Finset.range N).image k = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (hk t (Finset.mem_range.mp ht)).1
    · rw [Finset.card_image_of_injOn hinj]
  have : N - 1 ∈ (Finset.range N).image k := by rw [himg]; simp; omega
  obtain ⟨t, ht, e⟩ := Finset.mem_image.mp this
  have ht' := Finset.mem_range.mp ht
  refine ⟨t, ht', ?_⟩
  rw [(hk t ht').2, e]
  have : N - 1 + 1 = N := by omega
  simp [union_apply, single_apply, this]

/-! ## The critical section -/

/-- The cells a locked thread `t` owns: the resource for `S`, the lock's token heap and its
permit. -/
theorem cs_facts {N t : Nat} {S : Finset Nat} {htok : Heap} (hS : S ⊆ Finset.range N)
    (ht : t < N) (d12 : Heap.Disjoint (cH N S) htok)
    (d : Heap.Disjoint (Heap.union (cH N S) htok) (Heap.single (permit t) 0)) :
    t ∉ S ∧ S.card < N ∧ htok x = none ∧ htok (permit t) = none ∧
      (∀ k ∈ S, htok (permit k) = none) ∧ (∀ k, S.card ≤ k → k < N → htok (receipt k) = none) := by
  have hpt : Heap.union (cH N S) htok (permit t) = none := by
    rcases d (permit t) with e | e
    · exact e
    · simp [single_apply] at e
  have htS : t ∉ S := by
    intro hm
    have := (union_eq_none.mp hpt).1
    simp [cH, union_apply, hm] at this
  have hcard : S.card < N := by
    have hsub : S ⊆ (Finset.range N).erase t := by
      intro a ha
      exact Finset.mem_erase.mpr ⟨fun e => htS (e ▸ ha), hS ha⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr ht), Finset.card_range] at this
    omega
  refine ⟨htS, hcard, ?_, (union_eq_none.mp hpt).2, ?_, ?_⟩
  · rcases d12 x with e | e
    · simp [cH, union_apply, hcard] at e
    · exact e
  · intro k hk
    rcases d12 (permit k) with e | e
    · simp [cH, union_apply, hk] at e
    · exact e
  · intro k hk1 hk2
    rcases d12 (receipt k) with e | e
    · simp [cH, union_apply, hk1, hk2] at e
    · exact e

/-- **The heap after the increment**, re-split: the resource for `insert t S`, the token heap,
and the thread's receipt (with the counter if it wrote `N`). -/
theorem cs_heap {N t : Nat} {S : Finset Nat} {htok : Heap} (htS : t ∉ S) (hcard : S.card < N)
    (hx : htok x = none) (hpt : htok (permit t) = none)
    (hr : ∀ k, S.card ≤ k → k < N → htok (receipt k) = none) :
    (fun y => if y = x then some (S.card + 1) else
      Heap.union (Heap.union (cH N S) htok) (Heap.single (permit t) 0) y) =
    Heap.union (Heap.union (cH N (insert t S)) htok)
      (Heap.union (Heap.single (receipt S.card) 0) (xH (decide (S.card + 1 = N)) N)) := by
  have hc : (insert t S).card = S.card + 1 := Finset.card_insert_of_notMem htS
  funext y
  rcases classify y with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨hy, ho⟩
  · simp only [ite_true]
    by_cases e : S.card + 1 < N
    · simp [cH, union_apply, hc, e]
    · have e' : S.card + 1 = N := by omega
      simp [cH, union_apply, hc, e', hx, single_apply]
  · by_cases hk : k = t
    · subst hk; simp [cH, union_apply, htS, hpt, single_apply]
    · simp [cH, union_apply, hk, single_apply]
  · by_cases hk : k = S.card
    · subst hk
      have : ¬ (S.card + 1 ≤ S.card) := by omega
      simp [cH, union_apply, hc, hcard, hr _ le_rfl hcard, single_apply, this]
    · have : (S.card ≤ k ∧ k < N) ↔ (S.card + 1 ≤ k ∧ k < N) := by omega
      simp [cH, union_apply, hc, hk, single_apply, this]
  · have hp : ∀ j, y ≠ permit j := by
      intro j e; subst e; have := (ho {j} 0 0).1; simp at this
    simp only [hy, ite_false, cH, union_apply, xH_other hy, (ho _ 0 0).1,
      (ho S S.card N).2, (ho S (S.card + 1) N).2, hc]
    have h1 : rH S.card N y = none := (ho S S.card N).2
    have h2 : rH (S.card + 1) N y = none := (ho S (S.card + 1) N).2
    have h3 : Heap.single (permit t) 0 y = none := by simp [single_apply, hp t]
    have h4 : Heap.single (receipt S.card) 0 y = none := by
      simp only [single_apply]; rw [ite_none]; intro e; subst e
      exact absurd (ho S S.card N).2 (by simp [hcard])
    simp [h3, h4, Option.or]

/-- The re-split resource is disjoint from the token heap. -/
theorem cs_disj_tok {N t : Nat} {S : Finset Nat} {htok : Heap} (htS : t ∉ S)
    (hx : htok x = none) (hpt : htok (permit t) = none) (hp : ∀ k ∈ S, htok (permit k) = none)
    (hr : ∀ k, S.card ≤ k → k < N → htok (receipt k) = none) :
    Heap.Disjoint (cH N (insert t S)) htok := by
  have hc : (insert t S).card = S.card + 1 := Finset.card_insert_of_notMem htS
  intro y
  rcases classify y with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨hy, ho⟩
  · exact .inr hx
  · by_cases hk : k = t
    · subst hk; exact .inr hpt
    · by_cases hkS : k ∈ S
      · exact .inr (hp k hkS)
      · exact .inl (by simp [cH, union_apply, hk, hkS])
  · by_cases hk : S.card + 1 ≤ k ∧ k < N
    · exact .inr (hr k (by omega) hk.2)
    · exact .inl (by simp [cH, union_apply, hc]; omega)
  · exact .inl (by simp [cH, union_apply, xH_other hy, (ho _ 0 0).1, (ho S (S.card + 1) N).2, hc])

/-- The receipt (and counter) taken out is disjoint from the re-split resource and the token
heap. -/
theorem cs_disj_own {N t : Nat} {S : Finset Nat} {htok : Heap} (htS : t ∉ S) (hcard : S.card < N)
    (hx : htok x = none) (hr : ∀ k, S.card ≤ k → k < N → htok (receipt k) = none) :
    Heap.Disjoint (Heap.union (cH N (insert t S)) htok)
      (Heap.union (Heap.single (receipt S.card) 0) (xH (decide (S.card + 1 = N)) N)) := by
  have hc : (insert t S).card = S.card + 1 := Finset.card_insert_of_notMem htS
  intro y
  rcases classify y with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨hy, ho⟩
  · by_cases e : S.card + 1 = N
    · exact .inl (by simp [cH, union_apply, hc, e, hx])
    · exact .inr (by simp [union_apply, single_apply, e])
  · exact .inr (by simp [union_apply, single_apply])
  · by_cases hk : k = S.card
    · subst hk; exact .inl (by simp [cH, union_apply, hc, hr _ le_rfl hcard])
    · exact .inr (by simp [union_apply, single_apply, hk])
  · refine .inr ?_
    have : y ≠ receipt S.card := by
      intro e; subst e; exact absurd (ho S S.card N).2 (by simp [hcard])
    simp [union_apply, single_apply, this, xH_other hy]

theorem lit_eval (a : Nat) (h : a < 2 ^ 64) (rs : Regs) : ((Expr.lit a).eval rs).toNat = a := by
  simp [Expr.eval]; omega

/-- **The critical section** `inc` from the locked heap: it reads `|S|` and writes `|S| + 1`. -/
theorem inc_safe {I : HProp} {Q : Regs → HProp} {N t : Nat} (hN : N < 2 ^ 64) {S : Finset Nat}
    {htok : Heap} (hcard : S.card < N) {rs : Regs}
    (hq : ∀ rs', Q rs' (fun y => if y = x then some (S.card + 1) else
      Heap.union (Heap.union (cH N S) htok) (Heap.single (permit t) 0) y)) :
    Csl.Safe I Q inc rs (Heap.union (Heap.union (cH N S) htok) (Heap.single (permit t) 0)) := by
  have hX : Heap.union (Heap.union (cH N S) htok) (Heap.single (permit t) 0) x =
      some S.card := by
    simp [cH, union_apply, hcard]
  apply safe_seq
  apply safe_load_na (v := S.card) (by rw [lit_eval x (by decide)]; exact hX)
  apply safe_store_na (by rw [lit_eval x (by decide), hX]; rfl)
  rw [updH_wr, lit_eval x (by decide)]
  have hv : ((Expr.bin .add (.reg .rbx) (.lit 1)).eval
      (rs.set .rbx (BitVec.ofNat 64 S.card))).toNat % 2 ^ (8 * 8) = S.card + 1 := by
    simp [Expr.eval, BinOp.eval, Regs.set, BitVec.toNat_add]
    omega
  rw [hv]
  exact hq _

/-! ## A silent assignment (the rules, restated) -/

theorem labOk_mono {I : HProp} {K K' : Heap → Prop} (hK : ∀ h, K h → K' h) {l : Lab} {h : Heap}
    (H : LabOk I K l h) : LabOk I K' l h := by
  obtain ⟨hm, hna, hat⟩ := H
  refine ⟨hm, fun hn => ⟨(hna hn).1, fun hok => hK _ ((hna hn).2 hok)⟩, fun hn hI hIi hd => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hat hn hI hIi hd
  refine ⟨h1, h2, fun hok => ?_⟩
  obtain ⟨h', hI', a, b, c, d, e⟩ := h3 hok
  exact ⟨h', hI', a, b, c, hK _ d, e⟩

theorem safeF_mono {I : HProp} {Q : Regs → HProp} {R R' : Stmt → Regs → Heap → Prop}
    (hR : ∀ s rs h, R s rs h → R' s rs h) {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q R s rs h) : SafeF I Q R' s rs h :=
  ⟨H.1, fun s' rs' hs => hR _ _ _ (H.2.1 s' rs' hs),
    fun l s' rs' hs => labOk_mono (hR _ _) (H.2.2 l s' rs' hs)⟩

theorem safe_post {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : Csl.Safe I Q s rs h) : SafeF I Q (Csl.Safe I Q) s rs h := by
  obtain ⟨R, hR, hpost⟩ := H
  exact safeF_mono (fun s rs h hr => ⟨R, hr, hpost⟩) (hpost _ _ _ hR)

theorem safe_intro {I : HProp} {Q : Regs → HProp} {s : Stmt} {rs : Regs} {h : Heap}
    (H : SafeF I Q (Csl.Safe I Q) s rs h) : Csl.Safe I Q s rs h := by
  refine ⟨fun s' rs' h' => (s' = s ∧ rs' = rs ∧ h' = h) ∨ Csl.Safe I Q s' rs' h',
    Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
  rintro s' rs' h' (⟨rfl, rfl, rfl⟩ | hs)
  · exact safeF_mono (fun _ _ _ x => Or.inr x) H
  · exact safeF_mono (fun _ _ _ x => Or.inr x) (safe_post hs)

/-- **A silent register assignment.** -/
theorem safe_assign {I : HProp} {Q : Regs → HProp} {d : Reg} {e : Expr} {rs : Regs} {h : Heap}
    (hq : Q (rs.set d (e.eval rs)) h) : Csl.Safe I Q (.assign d e) rs h := by
  refine safe_intro ⟨(fun e => by cases e), (fun s' rs' hs => ?_), (fun l s' rs' hs => by cases hs)⟩
  cases hs
  exact safe_skip hq

/-! ## One thread, the logic -/

/-- The client's invariant at `M`. -/
def cInv (M : Iface) (N : Nat) : HProp := M.inv m (R N) ∗ hemp

theorem rdi_m (rs : Regs) : ((rs.set .rdi ((Expr.lit m).eval rs)) .rdi).toNat = m := by
  simp [Regs.set, Expr.eval, m]

/-- **One thread is safe**, for every mutex meeting the interface. -/
theorem thread_safe (M : Iface) (N L : Nat) (hN : N < 2 ^ 64) {t : Nat} (ht : t < N) :
    Csl.Safe (cInv M N) (post N t) (body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (permit t) 0) := by
  apply safe_seq
  apply safe_seq
  apply safe_assign
  have H := safe_frame (F := fun h => h = Heap.single (permit t) 0)
    (M.lock_spec m (R N) hemp L _ (rdi_m Regs.zero)) (disjoint_empty _) rfl
  rw [union_empty_left] at H
  refine safe_conseq (fun rs h hp => ?_) H
  obtain ⟨h12, hF, d, rfl, hRL, rfl⟩ := hp
  obtain ⟨hR, htok, d12, rfl, ⟨S, hS, rfl⟩, htk⟩ := hRL
  obtain ⟨htS, hcard, hx, hpt, hp, hr⟩ := cs_facts hS ht d12 d
  apply safe_seq
  refine inc_safe hN hcard (fun rs' => ?_)
  rw [cs_heap htS hcard hx hpt hr]
  apply safe_seq
  apply safe_assign
  have U := safe_frame
    (F := fun h => h = Heap.union (Heap.single (receipt S.card) 0) (xH (decide (S.card + 1 = N)) N))
    (M.unlock_spec m (R N) hemp L _ (Heap.union (cH N (insert t S)) htok) (rdi_m rs')
      ⟨_, htok, cs_disj_tok htS hx hpt hp hr, rfl,
        ⟨insert t S, Finset.insert_subset (Finset.mem_range.mpr ht) hS, rfl⟩, htk⟩)
    (cs_disj_own htS hcard hx hr) rfl
  refine safe_conseq (fun rs'' h hp => ?_) U
  obtain ⟨h₁, h₂, -, rfl, e1, rfl⟩ := hp
  cases e1
  exact ⟨S.card, hcard, union_empty_left _⟩

/-! ## The certificate, the logic -/

/-- Thread `t` starts owning its permit. -/
def own (N t : Nat) : Heap := if t < N then Heap.single (permit t) 0 else Heap.empty

/-- The invariant's start: the unlocked mutex and the resource for `∅`. -/
def hI0 (init : Heap) (N : Nat) : Heap := Heap.union init (cH N ∅)

theorem init_far {init : Heap} (hdom : ∀ a, (init a).isSome → m ≤ a ∧ a < m + 8) {a : Nat}
    (ha : a < m ∨ m + 8 ≤ a) : init a = none := by
  cases e : init a with
  | none => rfl
  | some w => have := hdom a (by simp [e]); omega

theorem permit_far (k : Nat) : m + 8 ≤ permit k := by simp [permit, m, tb]; omega
theorem receipt_far (k : Nat) : m + 8 ≤ receipt k := by simp [receipt, m, tb]; omega
theorem x_far : m + 8 ≤ x := by decide

theorem mem_permit {N k : Nat} (hk : k < N) : mem N (permit k) = some 0 := by
  simp only [mem]; rw [ite_some]; right; simp only [isTok, permit]; omega

theorem mem_receipt {N k : Nat} (hk : k < N) : mem N (receipt k) = some 0 := by
  simp only [mem]; rw [ite_some]; right; simp only [isTok, receipt]; omega

theorem mem_x (N : Nat) : mem N x = some 0 := by simp [mem]

theorem mem_low {N a : Nat} (ha : a < m + 8) : mem N a = none := by
  simp only [mem]; rw [ite_none]; simp only [isTok, x, m, tb] at ha ⊢; omega

/-- The certificate's heaps (common to both logics). -/
theorem cert_heaps {init : Heap} (hdom : ∀ a, (init a).isSome → m ≤ a ∧ a < m + 8) (N : Nat) :
    (∀ t u, t ≠ u → Heap.Disjoint (own N t) (own N u)) ∧
    (∀ t, Heap.Disjoint (own N t) (hI0 init N)) ∧
    (∀ t, Heap.Le (own N t) (Heap.union (mem N) (Heap.union init Heap.empty))) ∧
    Heap.Le (hI0 init N) (Heap.union (mem N) (Heap.union init Heap.empty)) ∧
    Heap.Disjoint init (cH N ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t u htu y
    unfold own
    by_cases ht : t < N
    · by_cases hy : y = permit t
      · subst hy; right; split <;> simp [single_apply, empty_apply, htu]
      · left; simp [ht, single_apply, hy]
    · left; simp [ht, empty_apply]
  · intro t y
    unfold own
    by_cases ht : t < N
    · by_cases hy : y = permit t
      · subst hy; right
        simp [hI0, union_apply, init_far hdom (Or.inr (permit_far t)), cH]
      · left; simp [ht, single_apply, hy]
    · left; simp [ht, empty_apply]
  · intro t a v hv
    unfold own at hv
    split at hv
    · rename_i ht
      simp only [single_apply] at hv
      split at hv
      · rename_i e; subst e; cases hv
        simp [union_apply, mem_permit ht]
      · cases hv
    · cases hv
  · intro a v hv
    simp only [hI0, union_apply] at hv
    cases e : init a with
    | some w =>
      rw [e] at hv; cases hv
      have := hdom a (by simp [e])
      simp [union_apply, mem_low (N := N) (a := a) (by omega), e]
    | none =>
      rw [e] at hv
      simp only [Option.none_or] at hv
      rcases classify a with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨ha, ho⟩
      · by_cases hN : 0 < N
        · simp [cH, union_apply, hN] at hv; subst hv; simp [union_apply, mem_x]
        · simp [cH, union_apply, hN] at hv
      · simp [cH, union_apply] at hv
      · by_cases hk : k < N
        · simp [cH, union_apply, hk] at hv; subst hv; simp [union_apply, mem_receipt hk]
        · simp [cH, union_apply, hk] at hv
      · simp [cH, union_apply, xH_other ha, (ho ∅ 0 N).1, (ho ∅ 0 N).2] at hv
  · intro y
    rcases classify y with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨hy, ho⟩
    · exact .inl (init_far hdom (Or.inr x_far))
    · exact .inl (init_far hdom (Or.inr (permit_far k)))
    · exact .inl (init_far hdom (Or.inr (receipt_far k)))
    · exact .inr (by simp [cH, union_apply, xH_other hy, (ho ∅ 0 N).1, (ho ∅ 0 N).2])

theorem R_empty (N : Nat) : R N (cH N ∅) := ⟨∅, Finset.empty_subset _, rfl⟩

/-- **The counter client's certificate at every mutex meeting the interface.** -/
theorem counter_ginv (M : Iface) (hM : M.size ≤ 8) (N L : Nat) (hN : N < 2 ^ 64) :
    GInv (cInv M N) (post N) N ((client N).link M L) (own N) (hI0 (M.init m) N) := by
  have hdom : ∀ a, (M.init m a).isSome → m ≤ a ∧ a < m + 8 := fun a h => by
    have := M.init_dom m a h; omega
  obtain ⟨d1, d2, l1, l2, dI⟩ := cert_heaps hdom N
  refine ⟨d1, d2, l1, l2, sep_iff_emp ?_, ?_⟩
  · exact M.init_inv m (R N) _ (R_empty N) dI
  · intro t ht
    have : ((client N).link M L).ts t = (body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Mutex.Client.link, Mutex.Client.startWith, client, ht]
    rw [this]
    have : own N t = Heap.single (permit t) 0 := by simp [own, ht]
    rw [this]
    exact thread_safe M N L hN ht
where
  sep_iff_emp {P : HProp} {h : Heap} (H : P h) : (P ∗ hemp) h :=
    ⟨h, Heap.empty, disjoint_empty_right h, (union_empty_right h).symm, H, rfl⟩

/-! ## One thread, the logic with ghost state -/

/-- The empty `GProp`. -/
def gemp : GProp := fun h g => h = Heap.empty ∧ g = Heap.empty

/-- The client's invariant at `M : IfaceG`. -/
def gInv (M : IfaceG) (N : Nat) : GProp := gsep (M.inv m (R N)) gemp

/-- What thread `t` ends with, and a ready ghost heap. -/
def postG (M : IfaceG) (N t : Nat) : Bool → Regs → Heap → Heap → Prop :=
  fun _ rs h g => post N t rs h ∧ M.ready m g

/-- **One thread is `SafeR`**, for every mutex meeting the ghost-aware interface. -/
theorem thread_safeG (M : IfaceG) (hM : M.size ≤ 8) {N : Nat} (hN : M.thrOk N) (L : Nat)
    (hN64 : N < 2 ^ 64) {t : Nat} (ht : t < N) :
    SafeR (gInv M N) (postG M N t) false (body (M.lock L) (M.unlock L) t) Regs.zero
      (Heap.single (permit t) 0) (M.gthr m t) := by
  have hsz : m + M.size ≤ 2 ^ 64 := by simp only [m]; omega
  apply safeR_seq
  apply safeR_seq
  apply safeR_assign
  have H := safeR_frame (M.lock_spec m (R N) gemp L _ false (M.gthr m t) (rdi_m Regs.zero) hsz
    (M.ready_thr m N t hN ht)) (disjoint_empty (Heap.single (permit t) 0))
  rw [union_empty_left] at H
  refine safeR_conseq (fun p rs h g hp => ?_) H
  obtain ⟨h12, ⟨rfl, hRL⟩, d, rfl⟩ := hp
  obtain ⟨hR, htok, g₁, gtok, d12, rfl, -, rfl, ⟨⟨S, hS, rfl⟩, rfl⟩, htk⟩ := hRL
  obtain ⟨htS, hcard, hx, hpt, hp, hr⟩ := cs_facts hS ht d12 d
  apply safeR_seq
  have C := safeR_lift (I := gInv M N) (I0 := fun h => h = Heap.empty)
    (g := Heap.union Heap.empty gtok)
    (fun hI gI i => ⟨Heap.empty, hI, disjoint_empty _, (union_empty_left hI).symm, rfl,
      fun hA' e _ => by rw [e, union_empty_left]; exact i⟩)
    (inc_safe (I := fun h => h = Heap.empty) (Q := fun _ h => h =
      Heap.union (Heap.union (cH N (insert t S)) htok)
        (Heap.union (Heap.single (receipt S.card) 0) (xH (decide (S.card + 1 = N)) N)))
      (t := t) hN64 hcard (rs := rs) (fun _ => cs_heap htS hcard hx hpt hr))
  refine safeR_conseq (fun p rs' h g hp => ?_) C
  obtain ⟨rfl, rfl, rfl⟩ := hp
  apply safeR_seq
  apply safeR_assign
  have U := safeR_frame (M.unlock_spec m (R N) gemp L _ (Heap.union (cH N (insert t S)) htok)
    (Heap.union Heap.empty gtok) (rdi_m rs') hsz
    ⟨cH N (insert t S), htok, Heap.empty, gtok, cs_disj_tok htS hx hpt hp hr, rfl,
      disjoint_empty _, rfl,
      ⟨⟨insert t S, Finset.insert_subset (Finset.mem_range.mpr ht) hS, rfl⟩, rfl⟩, htk⟩)
    (cs_disj_own htS hcard hx hr)
  refine safeR_conseq (fun p rs'' h g hp => ?_) U
  obtain ⟨h1, ⟨rfl, hrd⟩, -, rfl⟩ := hp
  exact ⟨⟨S.card, hcard, union_empty_left _⟩, hrd⟩

/-- **The counter client's certificate at every mutex meeting the ghost-aware interface.** -/
theorem counter_ginvG (M : IfaceG) (hM : M.size ≤ 8) {N : Nat} (hN : M.thrOk N) (L : Nat)
    (hN64 : N < 2 ^ 64) :
    GInvR (gInv M N) (postG M N) N ((client N).linkG M L) (own N) (M.gthr m)
      (hI0 (M.init m) N) (M.ginit m) := by
  have hdom : ∀ a, (M.init m a).isSome → m ≤ a ∧ a < m + 8 := fun a h => by
    have := M.init_dom m a h; omega
  obtain ⟨d1, d2, l1, l2, dI⟩ := cert_heaps hdom N
  refine ⟨d1, d2, fun t u h => M.gthr_disj m t u h, fun t => ?_, l1, l2, ?_, ?_⟩
  · intro a; exact (M.ginit_disj m t a).symm
  · exact ⟨hI0 (M.init m) N, Heap.empty, M.ginit m, Heap.empty, disjoint_empty_right _,
      (union_empty_right _).symm, disjoint_empty_right _, (union_empty_right _).symm,
      M.init_inv m (R N) _ (R_empty N) dI, rfl, rfl⟩
  · intro t ht
    have : ((client N).linkG M L).ts t = (body (M.lock L) (M.unlock L) t, Regs.zero) := by
      simp [Mutex.Client.linkG, Mutex.Client.startWith, client, ht]
    rw [this]
    have : own N t = Heap.single (permit t) 0 := by simp [own, ht]
    rw [this]
    exact thread_safeG M hM hN L hN64 ht

/-! ## Adequacy -/

/-- **The counter is `N`** on CIR's native TSO and XL machines, for every mutex meeting the
interface. -/
theorem counter_link (M : Iface) (hM : M.size ≤ 8) {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64)
    (L : Nat) {model : OModel} {Cf : OCfg}
    (hr : OReach model N ((client N).link M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem := by
  obtain ⟨hs', hI', q, -, dp, -, le, -⟩ := csl_buffered (counter_ginv M hM N L hN) hr hd hf
  obtain ⟨t, -, e⟩ := count hN0 (fun t ht => q t ht) dp
  exact le t x N e

/-- **The counter is `N`** on CIR's SC machine, for every mutex meeting the interface. -/
theorem counter_link_sc (M : Iface) (hM : M.size ≤ 8) {N : Nat} (hN0 : 0 < N) (hN : N < 2 ^ 64)
    (L : Nat) {Cf : Cfg} (hr : ScReach N ((client N).link M L) Cf) (hf : Cf.Done N) :
    Goal N Cf.mem := by
  obtain ⟨hs', hI', q, -, dp, -, le, -⟩ := (csl_sc (counter_ginv M hM N L hN) hr).2 hf
  obtain ⟨t, -, e⟩ := count hN0 (fun t ht => q t ht) dp
  exact le t x N e

/-- **The counter is `N`** on CIR's native TSO machine, for every mutex meeting the ghost-aware
interface. -/
theorem counter_linkG (M : IfaceG) (hM : M.size ≤ 8) {N : Nat} (hN : M.thrOk N) (hN0 : 0 < N)
    (hN64 : N < 2 ^ 64) (L : Nat) {Cf : OCfg}
    (hr : OReach .tso N ((client N).linkG M L).toO Cf) (hd : Cf.Drained)
    (hf : ∀ t < N, (Cf.ts t).1 = .skip) : Goal N Cf.mem := by
  obtain ⟨hs', gs', hI', gI', ps', q, -, le, -, dp, -, -⟩ :=
    rel_tso (G0 := Heap.empty) (counter_ginvG M hM hN L hN64) (fun c h => by simp [empty_apply] at h)
      hr hd hf
  obtain ⟨t, -, e⟩ := count hN0 (fun t ht => (q t ht).1) dp
  exact le t x N e

end Silmaril.Proofs.X86.Concurrency.Story
