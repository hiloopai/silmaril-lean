module

public import Silmaril.Wasm.Jco.Resource.Scope.Defs
public import Silmaril.Wasm.Jco.Resource.Handle.Thms

/-!
# Full handles: invariants of computations, and the table

* `Keeps I m`: every returning run of `m` from a state whose second component satisfies `I`
  ends in one; `keeps_pure`, `keeps_fail`, `keeps_bind`, `keeps_onFst`, `keeps_ofTab`,
  `keeps_check`, `keeps_ofOption`;
* `countB_add`, `countB_remove`, `countB_modLends`: how the borrow count changes;
* `inv_add`, `inv_remove`, `inv_modLends`, `inv_borrows_dec`: the invariant `FSt.Inv`;
* `countB_zero`: a zero count means no live borrow entry below `next`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Res.Scope

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res Silmaril.Wasm.Jco.Res.Scope
open Silmaril.Wasm.Jco.RM

variable {σ τ α β : Type}

/-- Every returning run from a state whose second component satisfies `I` ends in one. -/
def Keeps (I : τ → Prop) (m : RM (σ × τ) α) : Prop :=
  ∀ st a st', I st.2 → m st (.ok a st') → I st'.2

theorem keeps_pure {I : τ → Prop} (a : α) : Keeps I (pure a : RM (σ × τ) α) := by
  intro st b st' hI h
  have he : st' = st := (Out.ok.inj h).2
  rw [he]
  exact hI

theorem keeps_fail {I : τ → Prop} : Keeps I (fail : RM (σ × τ) α) := by
  intro _ _ _ _ h
  cases h

theorem keeps_bind {I : τ → Prop} {m : RM (σ × τ) α} {k : α → RM (σ × τ) β}
    (hm : Keeps I m) (hk : ∀ a, Keeps I (k a)) : Keeps I (m >>= k) := by
  intro st b st' hI h
  rcases h with ⟨a, st1, h1, h2⟩ | ⟨_, h⟩
  · exact hk a st1 b st' (hm st a st1 hI h1) h2
  · cases h

theorem keeps_onFst {I : τ → Prop} (m : RM σ α) : Keeps I (m.onFst : RM (σ × τ) α) := by
  intro st a st' hI h
  have he : st'.2 = st.2 := h.2
  rw [he]
  exact hI

theorem keeps_check {I : τ → Prop} (b : Bool) : Keeps I (check b : RM (σ × τ) Unit) := by
  cases b
  · exact keeps_fail
  · exact keeps_pure ()

theorem keeps_ofOption {I : τ → Prop} (x : Option α) : Keeps I (ofOption x : RM (σ × τ) α) := by
  cases x
  · exact keeps_fail
  · exact keeps_pure _

theorem ofTab_ok {f : τ → Option (α × τ)} {st : σ × τ} {a : α} {st' : σ × τ}
    (h : RM.ofTab f st (.ok a st')) : ∃ t', f st.2 = some (a, t') ∧ st' = (st.1, t') := by
  unfold RM.ofTab at h
  cases hf : f st.2 with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    have h' := Out.ok.inj h
    exact ⟨p.2, by rw [h'.1], h'.2⟩

theorem keeps_ofTab {I : τ → Prop} {f : τ → Option (α × τ)}
    (hf : ∀ t a t', I t → f t = some (a, t') → I t') : Keeps I (RM.ofTab f : RM (σ × τ) α) := by
  intro st a st' hI h
  obtain ⟨t', hft, rfl⟩ := ofTab_ok h
  exact hf _ a t' hI hft

/-! ## The borrow count -/

/-- `1` for a live borrow entry. -/
def isB : Option FEntry → Nat
  | some e => if e.own then 0 else 1
  | none => 0

theorem countB_succ (t : Nat → Option FEntry) (n : Nat) :
    FSt.countB t (n + 1) = FSt.countB t n + isB (t n) := by
  show FSt.countB t n + _ = _
  cases t n <;> rfl

theorem countB_congr {t t' : Nat → Option FEntry} :
    ∀ n, (∀ j, j < n → isB (t' j) = isB (t j)) → FSt.countB t' n = FSt.countB t n
  | 0, _ => rfl
  | n + 1, h => by
    rw [countB_succ, countB_succ, countB_congr n (fun j hj => h j (by omega)), h n (by omega)]

/-- Removing entry `i` lowers the count by its borrowness, once `i` is below the bound. -/
theorem countB_remove (t : Nat → Option FEntry) (i : Nat) :
    ∀ n, FSt.countB (fun j => if j = i then none else t j) n + (if i < n then isB (t i) else 0) =
      FSt.countB t n
  | 0 => by simp [FSt.countB]
  | n + 1 => by
    have ih := countB_remove t i n
    rw [countB_succ, countB_succ, ← ih]
    by_cases hn : n = i
    · subst hn
      simp [isB]
    · have hlt : (i < n + 1) = (i < n) := by
        apply propext
        omega
      simp only [hn, ↓reduceIte, hlt]
      omega

theorem countB_zero {t : Nat → Option FEntry} :
    ∀ {n}, FSt.countB t n = 0 → ∀ j, j < n → isB (t j) = 0
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    rw [countB_succ] at h
    by_cases hjn : j = n
    · rw [hjn]
      omega
    · have h0 : FSt.countB t n = 0 := by omega
      exact countB_zero h0 j (by omega)

/-! ## The invariant -/

theorem add_facts {s : FSt} (hI : s.Inv) (e : FEntry) :
    (∀ j, (s.add e).2.next ≤ j → (s.add e).2.tab j = none) ∧
      FSt.countB (s.add e).2.tab (s.add e).2.next = s.borrows + isB (some e) := by
  have hbelow : ∀ j, j < s.next → isB ((s.add e).2.tab j) = isB (s.tab j) := by
    intro j hj
    have hne : j ≠ s.next := by omega
    simp [FSt.add, hne]
  have hc : FSt.countB (s.add e).2.tab (s.add e).2.next = s.borrows + isB (some e) := by
    show FSt.countB (s.add e).2.tab (s.next + 1) = _
    rw [countB_succ, countB_congr s.next hbelow, ← hI.2]
    simp [FSt.add]
  refine ⟨fun j hj => ?_, hc⟩
  have hj' : s.next ≤ j := by simp [FSt.add] at hj; omega
  have hne : j ≠ s.next := by simp [FSt.add] at hj; omega
  simp [FSt.add, hne, hI.1 j hj']

theorem inv_add_own {s : FSt} (hI : s.Inv) {e : FEntry} (he : e.own = true) : (s.add e).2.Inv := by
  obtain ⟨h1, h2⟩ := add_facts hI e
  refine ⟨h1, ?_⟩
  rw [h2]
  simp [isB, he, FSt.add]

theorem inv_add_borrow {s : FSt} (hI : s.Inv) {e : FEntry} (he : e.own = false) :
    ({ (s.add e).2 with borrows := (s.add e).2.borrows + 1 } : FSt).Inv := by
  obtain ⟨h1, h2⟩ := add_facts hI e
  refine ⟨h1, ?_⟩
  show (s.add e).2.borrows + 1 = FSt.countB (s.add e).2.tab (s.add e).2.next
  rw [h2]
  simp [isB, he, FSt.add]

theorem inv_remove {s : FSt} (hI : s.Inv) {i : Nat} {e : FEntry} {s' : FSt}
    (h : s.remove? i = some (e, s')) :
    s.tab i = some e ∧ (∀ j, s'.next ≤ j → s'.tab j = none) ∧
      FSt.countB s'.tab s'.next + isB (some e) = s.borrows ∧ s'.borrows = s.borrows := by
  unfold FSt.remove? at h
  cases hi : s.tab i with
  | none => rw [hi] at h; cases h
  | some e' =>
    rw [hi] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hlt : i < s.next := by
      by_contra hc
      rw [hI.1 i (by omega)] at hi
      cases hi
    have hr := countB_remove s.tab i s.next
    simp only [hlt, ↓reduceIte, hi] at hr
    refine ⟨rfl, fun j hj => ?_, ?_, rfl⟩
    · have hj' : s.next ≤ j := hj
      simp [FSt.removed, hI.1 j hj']
    · show FSt.countB (fun j => if j = i then none else s.tab j) s.next + _ = _
      rw [hr, hI.2]

theorem inv_modLends {s : FSt} (hI : s.Inv) (i : Nat) (f : Nat → Nat) : (s.modLends i f).Inv := by
  have hb : ∀ j, j < s.next → isB ((s.modLends i f).tab j) = isB (s.tab j) := by
    intro j _
    by_cases hj : j = i
    · subst hj
      cases h : s.tab j <;> simp [FSt.modLends, h, isB]
    · simp [FSt.modLends, hj]
  refine ⟨fun j hj => ?_, ?_⟩
  · have hj' : s.next ≤ j := hj
    by_cases hji : j = i
    · subst hji
      simp [FSt.modLends, hI.1 j hj']
    · simp [FSt.modLends, hji, hI.1 j hj']
  · show s.borrows = FSt.countB (s.modLends i f).tab s.next
    rw [countB_congr s.next hb, hI.2]

end Silmaril.Proofs.Wasm.Jco.Res.Scope
