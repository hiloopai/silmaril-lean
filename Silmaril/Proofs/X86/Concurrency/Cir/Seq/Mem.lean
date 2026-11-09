module

public import Silmaril.X86.Concurrency.Cir.Seq.Defs

/-!
# The single-threaded lift: last writes and unit replay

Pure list facts:

* `lastW_some`, `lastW_none`, `lastW_eq`: `lastW evs y k` is the largest index below `k` of a
  write unit covering `y`;
* `before_*`: facts about `before` (position order in a list);
* `uReplay_take`: replaying the first `k` units succeeds exactly when every read unit among them
  finds `memAt` bytes, and then gives `memAt k`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte dummyEv)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec before)

/-! ## `lastW` -/

/-- A write unit covering `y`. -/
def WC (evs : List Ev) (y j : Nat) : Prop :=
  ∃ h : j < evs.length, evs[j].isW = true ∧ evs[j].covers y = true

theorem lastW_some {evs : List Ev} {y : Nat} :
    ∀ {k i : Nat}, lastW evs y k = some i → i < k ∧ WC evs y i ∧ ∀ j, i < j → j < k → ¬ WC evs y j
  | 0, _, h => by simp [lastW] at h
  | k + 1, i, h => by
    simp only [lastW] at h
    by_cases hk : k < evs.length
    · rw [List.getElem?_eq_getElem hk] at h
      simp only at h
      split at h
      · rename_i hw
        cases h
        simp only [Bool.and_eq_true] at hw
        refine ⟨Nat.lt_succ_self _, ⟨hk, hw⟩, fun j h1 h2 => ?_⟩
        omega
      · rename_i hw
        obtain ⟨h1, h2, h3⟩ := lastW_some h
        refine ⟨by omega, h2, fun j hj1 hj2 hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hj2 | rfl
        · exact h3 j hj1 hj2 hj
        · obtain ⟨_, a, b⟩ := hj
          simp [a, b] at hw
    · rw [List.getElem?_eq_none (by omega)] at h
      obtain ⟨h1, h2, h3⟩ := lastW_some h
      refine ⟨by omega, h2, fun j hj1 hj2 hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hj2 | rfl
      · exact h3 j hj1 hj2 hj
      · exact hk hj.1

theorem lastW_none {evs : List Ev} {y : Nat} :
    ∀ {k : Nat}, lastW evs y k = none → ∀ j, j < k → ¬ WC evs y j
  | 0, _ => by intro j hj; omega
  | k + 1, h => by
    simp only [lastW] at h
    intro j hj hw
    by_cases hk : k < evs.length
    · rw [List.getElem?_eq_getElem hk] at h
      simp only at h
      split at h
      · cases h
      · rename_i hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact lastW_none h j hj hw
        · obtain ⟨_, a, b⟩ := hw
          simp [a, b] at hn
    · rw [List.getElem?_eq_none (by omega)] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact lastW_none h j hj hw
      · exact hk hw.1

theorem lastW_eq {evs : List Ev} {y k i : Nat} (hi : i < k) (hw : WC evs y i)
    (hmax : ∀ j, i < j → j < k → ¬ WC evs y j) : lastW evs y k = some i := by
  cases h : lastW evs y k with
  | none => exact absurd hw (lastW_none h i hi)
  | some i' =>
    obtain ⟨h1, h2, h3⟩ := lastW_some h
    congr 1
    rcases Nat.lt_trichotomy i i' with c | c | c
    · exact absurd h2 (hmax i' c h1)
    · exact c.symm
    · exact absurd hw (h3 i c hi)

theorem lastW_exists {evs : List Ev} {y k i : Nat} (hi : i < k) (hw : WC evs y i) :
    ∃ i', lastW evs y k = some i' ∧ i ≤ i' := by
  cases h : lastW evs y k with
  | none => exact absurd hw (lastW_none h i hi)
  | some i' =>
    obtain ⟨_, _, h3⟩ := lastW_some h
    refine ⟨i', rfl, ?_⟩
    rcases Nat.lt_or_ge i' i with c | c
    · exact absurd hw (h3 i c hi)
    · exact c

/-! ## `before` -/

theorem before_mem {l : List Nat} {a b : Nat} (h : before l a b = true) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp [before] at h
  | cons c l ih =>
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.contains_iff_mem.mp h)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem before_total {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    before l a b = true ∨ before l b a = true := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [before]
    rcases List.mem_cons.mp ha with rfl | ha'
    · left; simp only [beq_self_eq_true, ite_true]
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact List.contains_iff_mem.mpr hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · right; simp only [beq_self_eq_true, ite_true]; exact List.contains_iff_mem.mpr ha'
      · by_cases hca : c = a
        · subst hca; left; simp only [beq_self_eq_true, ite_true]; exact List.contains_iff_mem.mpr hb'
        · by_cases hcb : c = b
          · subst hcb; right; simp only [beq_self_eq_true, ite_true]
            exact List.contains_iff_mem.mpr ha'
          · simp only [beq_iff_eq, hca, hcb, ite_false]
            exact ih ha' hb'

/-- In a duplicate-free list every other element is before the last one. -/
theorem before_last {l : List Nat} (hnd : l.Nodup) {w : Nat} (hw : l.getLast? = some w) {a : Nat}
    (ha : a ∈ l) (haw : a ≠ w) : before l a w = true := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [before]
    rcases List.mem_cons.mp ha with rfl | ha'
    · simp only [beq_self_eq_true, ite_true]
      cases l with
      | nil => simp at hw; exact absurd hw.symm (Ne.symm haw)
      | cons d l =>
        rw [List.getLast?_cons_cons] at hw
        exact List.contains_iff_mem.mpr (List.mem_of_getLast? hw)
    · have hca : c ≠ a := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ha')
      simp only [beq_iff_eq, hca, ite_false]
      cases l with
      | nil => simp at ha'
      | cons d l =>
        rw [List.getLast?_cons_cons] at hw
        exact ih (List.nodup_cons.mp hnd).2 hw ha'

/-- In a list sorted by `<`, `before` follows the order. -/
theorem before_sorted {l : List Nat} (hs : l.Pairwise (· < ·)) {a b : Nat}
    (h : before l a b = true) : a < b := by
  induction l with
  | nil => simp [before] at h
  | cons c l ih =>
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact List.rel_of_pairwise_cons hs (List.contains_iff_mem.mp h)
    · exact ih hs.of_cons h

/-- In a sorted list, a smaller element is before a larger one. -/
theorem before_of_lt {l : List Nat} (hs : l.Pairwise (· < ·)) {a b : Nat} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a < b) : before l a b = true := by
  rcases before_total ha hb (by omega) with h | h
  · exact h
  · exact absurd (before_sorted hs h) (by omega)

/-! ## Unit replay -/

theorem uReplay_append (m : Mem) (l l' : List (Ev × List Byte)) :
    uReplay m (l ++ l') = (uReplay m l).bind fun m' => uReplay m' l' := by
  induction l generalizing m with
  | nil => simp [uReplay]
  | cons u l ih =>
    simp only [List.cons_append, uReplay]
    cases uStep m u <;> simp [ih]

theorem lastW_succ {evs : List Ev} {y k : Nat} (hk : k < evs.length) :
    lastW evs y (k + 1) = if evs[k].isW && evs[k].covers y then some k else lastW evs y k := by
  simp only [lastW, List.getElem?_eq_getElem hk]

theorem getD_eq {evs : List Ev} {i : Nat} (h : i < evs.length) (d : Ev) : evs.getD i d = evs[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The memory after one more unit. -/
theorem memAt_succ {evs : List Ev} {m0 : Mem} {k : Nat} (hk : k < evs.length) :
    memAt evs m0 (k + 1) = if evs[k].isW then putBytes (memAt evs m0 k) evs[k].addr evs[k].size
      evs[k].data else memAt evs m0 k := by
  funext y
  simp only [memAt, lastW_succ hk]
  by_cases hw : evs[k].isW = true
  · simp only [hw, Bool.true_and, ite_true, putBytes]
    by_cases hc : evs[k].covers y = true
    · simp only [hc, ite_true, getD_eq hk, Ev.byte]
      simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp [hc]
    · simp only [hc]
      simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq, not_and] at hc
      have : ¬ (evs[k].addr ≤ y ∧ y < evs[k].addr + evs[k].size) := fun h => hc h.1 h.2
      simp [this, memAt]
  · simp [hw, memAt]

/-- A read unit checks the `memAt` bytes. -/
def ReadsAt (us : List (Ev × List Byte)) (m0 : Mem) (k : Nat) : Prop :=
  ∀ r (hr : r < us.length), r < k → us[r].1.isR = true →
    us[r].2 = bytesAt (memAt (us.map Prod.fst) m0 r) us[r].1.addr us[r].1.size

open Classical in
theorem uReplay_take (us : List (Ev × List Byte)) (m0 : Mem) :
    ∀ k, k ≤ us.length → uReplay m0 (us.take k) =
      if ReadsAt us m0 k then some (memAt (us.map Prod.fst) m0 k) else none
  | 0, _ => by
    have : ReadsAt us m0 0 := fun r _ h => absurd h (Nat.not_lt_zero _)
    simp only [List.take_zero, uReplay, this, ite_true]
    congr 1
  | k + 1, hk => by
    have hk' : k < us.length := hk
    rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some, uReplay_append,
      uReplay_take us m0 k (by omega)]
    have hl : k < (us.map Prod.fst).length := by simpa using hk'
    have hev : (us.map Prod.fst)[k] = us[k].1 := by simp
    by_cases hR : ReadsAt us m0 k
    · simp only [hR, ite_true, Option.bind_some, uReplay, uStep]
      rw [memAt_succ hl, hev]
      rcases hact : us[k].1.act with _ | _ | f
      · have hisR : us[k].1.isR = true := by simp [Ev.isR, hact]
        have hisW : us[k].1.isW = false := by simp [Ev.isW, hact]
        simp only [hisW]
        by_cases hb : bytesAt (memAt (us.map Prod.fst) m0 k) us[k].1.addr us[k].1.size = us[k].2
        · have : ReadsAt us m0 (k + 1) := by
            intro r hr hrk hrR
            rcases Nat.lt_succ_iff_lt_or_eq.mp hrk with hrk | rfl
            · exact hR r hr hrk hrR
            · exact hb.symm
          simp [hb, this]
        · have : ¬ ReadsAt us m0 (k + 1) := fun h => hb (h k hk' (Nat.lt_succ_self _) hisR).symm
          simp [hb, this]
      · have hisW : us[k].1.isW = true := by simp [Ev.isW, hact]
        have : ReadsAt us m0 (k + 1) := by
          intro r hr hrk hrR
          rcases Nat.lt_succ_iff_lt_or_eq.mp hrk with hrk | rfl
          · exact hR r hr hrk hrR
          · simp [Ev.isR, hact] at hrR
        simp [hisW, this]
      · have hisW : us[k].1.isW = false := by simp [Ev.isW, hact]
        have : ReadsAt us m0 (k + 1) := by
          intro r hr hrk hrR
          rcases Nat.lt_succ_iff_lt_or_eq.mp hrk with hrk | rfl
          · exact hR r hr hrk hrR
          · simp [Ev.isR, hact] at hrR
        simp [hisW, this]
    · have : ¬ ReadsAt us m0 (k + 1) := fun h => hR fun r hr hrk => h r hr (by omega)
      simp [hR, this]

open Classical in
/-- **Unit replay is `memAt`.** -/
theorem uReplay_iff (us : List (Ev × List Byte)) (m0 : Mem) {m : Mem} :
    uReplay m0 us = some m ↔ ReadsAt us m0 us.length ∧ m = memAt (us.map Prod.fst) m0 us.length := by
  have := uReplay_take us m0 us.length (le_refl _)
  rw [List.take_length] at this
  rw [this]
  by_cases h : ReadsAt us m0 us.length
  · simp [h, eq_comm]
  · simp [h]

end Silmaril.Proofs.X86.Concurrency.Cir.Seq
