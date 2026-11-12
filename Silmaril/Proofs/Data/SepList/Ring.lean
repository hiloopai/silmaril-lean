module

public import Silmaril.Proofs.Data.SepList.Dll

/-!
# Rings (circular doubly linked lists without sentinel): rotation, insertion, removal
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Data.SepList

open Silmaril.Data

theorem ring_cons_cons (K : Links) (x y : Nat) (xs : List Nat) :
    ring K (x :: y :: xs) = dseg K ((y :: xs).getLastD x) (x :: y :: xs) x := rfl

/-- **Rotation**: a ring's cells do not depend on where the list starts. -/
theorem mem_ring_rotate {K : Links} {c : Cell} (l₁ l₂ : List Nat) :
    c ∈ ring K (l₁ ++ l₂) → c ∈ ring K (l₂ ++ l₁) := by
  cases l₁ with
  | nil => simp
  | cons x xs =>
    cases l₂ with
    | nil => simp
    | cons y ys =>
      simp only [List.cons_append, ring, dseg_append, List.getLastD_cons, List.headD_cons]
      have e1 : (xs ++ y :: ys).getLastD x = ys.getLastD y := getLastD_append_cons xs
      have e2 : (ys ++ x :: xs).getLastD y = xs.getLastD x := getLastD_append_cons ys
      rw [e1, e2]
      rw [show x :: (xs ++ y :: ys) = (x :: xs) ++ (y :: ys) from rfl,
        show y :: (ys ++ x :: xs) = (y :: ys) ++ (x :: xs) from rfl, dseg_append, dseg_append]
      simp only [List.headD_cons, List.getLastD_cons, List.mem_append]
      exact Or.symm

theorem holds_ring_rotate {K : Links} {v : MemView} (l₁ l₂ : List Nat)
    (h : (ring K (l₁ ++ l₂)).Holds v) : (ring K (l₂ ++ l₁)).Holds v :=
  fun c hc => h c (mem_ring_rotate l₂ l₁ hc)

/-- Every node's two link cells are in the segment. -/
theorem dseg_has_slots (K : Links) : ∀ (p : Nat) (l : List Nat) (n : Nat) (x : Nat), x ∈ l →
    (∃ u, (⟨x + K.fd, K.ws, u⟩ : Cell) ∈ dseg K p l n) ∧ (∃ u, (⟨x + K.bk, K.ws, u⟩ : Cell) ∈ dseg K p l n)
  | _, [], _, _, h => nomatch h
  | p, y :: ys, n, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨⟨_, List.mem_cons_self ..⟩, ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩⟩
    · obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := dseg_has_slots K y ys n x h
      exact ⟨⟨u, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)⟩,
        ⟨w, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)⟩⟩

theorem ring_has_slots (K : Links) (l : List Nat) (x : Nat) (hx : x ∈ l) :
    (∃ u, (⟨x + K.fd, K.ws, u⟩ : Cell) ∈ ring K l) ∧ (∃ u, (⟨x + K.bk, K.ws, u⟩ : Cell) ∈ ring K l) := by
  cases l with
  | nil => exact nomatch hx
  | cons y ys => exact dseg_has_slots K _ _ _ x hx

/-- Link fields of the nodes of a holding ring are writable. -/
theorem ring_writable {K : Links} {v : MemView} {l : List Nat} (h : (ring K l).Holds v)
    {x : Nat} (hx : x ∈ l) : ∀ i < K.ws, v.writable (x + K.fd + i) = true ∧ v.writable (x + K.bk + i) = true := by
  obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := ring_has_slots K l x hx
  exact fun i hi => ⟨(h _ hu).2 i hi, (h _ hw).2 i hi⟩

/-- A retained ring cell, for `ringPushFront`: in `f` by `hcore`. -/
macro "core_cell" hcore:term:max : tactic =>
  `(tactic| (right; refine ⟨$hcore _ (by mem_frag) (by simp only []; omega) (by simp only []; omega), ?_, by addr_ne⟩;
             first | (apply inSlotsFd; simp; done) | (apply inSlotsBk; simp)))

/-- **Ring insertion at the front** (= anywhere, by rotation): `a` enters the ring `M` between
its last node and its head. The old fragment `f` only needs to contain the cells of `ring K M`
that do not change (the head's `bk`, the last node's `fd`): `f = ring K M` for an insertion,
`f = ring K (p :: M)` when `a` replaces `p`. -/
theorem ringPushFront {K : Links} {v : MemView} {f : Frag} {a : Nat} {M : List Nat} (hws : 0 < K.ws)
    (hf : f.Holds v) (hS : (K.slots (a :: M)).Sep) (hfit : ∀ x ∈ a :: M, x < 256 ^ K.ws)
    (hw : ∀ x ∈ a :: M, ∀ i < K.ws, v.writable (x + K.fd + i) = true ∧ v.writable (x + K.bk + i) = true)
    (hcore : ∀ c ∈ ring K M, c.addr ≠ M.headD 0 + K.bk → c.addr ≠ M.getLastD 0 + K.fd → c ∈ f) :
    (ring K (a :: M)).Holds (v.storeAll (ringInsertInto K a M)) := by
  obtain ⟨hnd, hx⟩ := Links.slotFacts hws hS
  have hnd' := hnd
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons, not_or] at hnd'
  cross a a
  have ha := hw a (by simp)
  cases M with
  | nil =>
    simp only [ringInsertInto, ↓reduceIte]
    refine Frag.holds_update (f := []) hS (fun _ h => nomatch h) ?_ ?_ ?_
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hfit a (by simp), fun i hi => (ha i hi).1, inSlotsFd (by simp)⟩
      · exact ⟨hfit a (by simp), fun i hi => (ha i hi).2, inSlotsBk (by simp)⟩
    · addr_ne
    · intro c hc
      simp only [ring, dseg, List.getLastD_nil, List.headD_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl <;> left <;> simp
  | cons m ms =>
    simp only [ringInsertInto, reduceCtorEq, ↓reduceIte]
    simp only [ringInsertStores, List.headD_cons, List.getLastD_cons] at hcore ⊢
    have hm := hw m (by simp)
    cross a m; cross m a; cross m m
    have ham : a ≠ m := by grind
    rcases List.eq_nil_or_concat ms with rfl | ⟨mid, z, rfl⟩
    · simp only [List.getLastD_nil]
      refine Frag.holds_update (f := []) hS (fun _ h => nomatch h) ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact ⟨hfit m (by simp), fun i hi => (ha i hi).1, inSlotsFd (by simp)⟩
        · exact ⟨hfit m (by simp), fun i hi => (ha i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit a (by simp), fun i hi => (hm i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit a (by simp), fun i hi => (hm i hi).1, inSlotsFd (by simp)⟩
      · addr_ne
      · intro c hc
        simp only [ring, dseg, List.getLastD_nil, List.getLastD_cons, List.headD_nil,
          List.headD_cons, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> left <;> simp
    · simp only [List.concat_eq_append] at *
      simp only [getLastD_concat] at hcore ⊢
      have hz := hw z (by simp)
      cross a z; cross z a; cross z z; cross m z; cross z m
      have haz : a ≠ z := by grind
      have hmz : m ≠ z := by grind
      have hT : ∀ x ∈ mid, x ∈ a :: m :: (mid ++ [z]) ∧ (x ≠ a ∧ x ≠ m ∧ x ≠ z ∧
          x + K.fd ≠ a + K.bk ∧ a + K.fd ≠ x + K.bk ∧ x + K.fd ≠ m + K.bk ∧ m + K.fd ≠ x + K.bk ∧
          x + K.fd ≠ z + K.bk ∧ z + K.fd ≠ x + K.bk ∧ x + K.fd ≠ x + K.bk) := fun x hxt => by
        have hxN : x ∈ a :: m :: (mid ++ [z]) := by simp [hxt]
        exact ⟨hxN, by grind, by grind, by grind, hx x hxN a (by simp), hx a (by simp) x hxN,
          hx x hxN m (by simp), hx m (by simp) x hxN, hx x hxN z (by simp), hx z (by simp) x hxN,
          hx x hxN x hxN⟩
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl | rfl | rfl
        · exact ⟨hfit m (by simp), fun i hi => (ha i hi).1, inSlotsFd (by simp)⟩
        · exact ⟨hfit z (by simp), fun i hi => (ha i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit a (by simp), fun i hi => (hm i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit a (by simp), fun i hi => (hz i hi).1, inSlotsFd (by simp)⟩
      · addr_ne
      · simp only [ring, List.append_assoc, List.cons_append, List.nil_append, dseg_append, dseg,
          List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, headD_append_cons,
          List.forall_mem_cons, List.forall_mem_append]
        refine ⟨by cell_tac, by cell_tac, by core_cell hcore, by cell_tac, ?_, by cell_tac,
          by core_cell hcore, ?_⟩
        · intro c hc
          obtain ⟨x, hxt, hw', ha'⟩ := mem_dseg hc
          obtain ⟨hxN, hfx⟩ := hT x hxt
          right
          refine ⟨hcore _ (by mem_frag_with hc) ?_ ?_, inSlots hxN hw' ha', ?_⟩ <;>
            rcases ha' with ha' | ha' <;> rw [ha'] <;> first | omega | addr_ne
        · simp

/-- The cells of `ring K M` other than its head's `bk` and its last node's `fd` are cells of
`ring K (p :: M)` (positional; no separation needed). -/
theorem ring_core_mem {K : Links} {c : Cell} {p : Nat} {M : List Nat} (hc : c ∈ ring K M)
    (h1 : c.addr ≠ M.headD 0 + K.bk) (h2 : c.addr ≠ M.getLastD 0 + K.fd) : c ∈ ring K (p :: M) := by
  cases M with
  | nil => exact nomatch hc
  | cons m ms =>
    rcases List.eq_nil_or_concat ms with rfl | ⟨mid, z, rfl⟩
    · simp only [ring, dseg, List.getLastD_nil, List.headD_nil, List.headD_cons, List.mem_cons,
        List.not_mem_nil, or_false] at hc h1 h2
      rcases hc with rfl | rfl
      · exact absurd rfl h2
      · exact absurd rfl h1
    · simp only [List.concat_eq_append] at hc h1 h2 ⊢
      simp only [ring, List.getLastD_cons, getLastD_concat, List.headD_cons, dseg, dseg_append,
        List.headD_nil, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc h1 h2 ⊢
      rcases hc with rfl | rfl | hc | rfl | rfl
      · simp
      · exact absurd rfl h1
      · simp [hc]
      · exact absurd rfl h2
      · simp

/-- **Ring removal at the front** (= anywhere, by rotation): `p` leaves the ring `p :: M`; its
successor's `bk` and its predecessor's `fd` are rewritten. -/
theorem ringPopFront {K : Links} {v : MemView} {p : Nat} {M : List Nat} (hws : 0 < K.ws)
    (hf : (ring K (p :: M)).Holds v) (hS : (K.slots (p :: M)).Sep)
    (hfit : ∀ x ∈ p :: M, x < 256 ^ K.ws) :
    (ring K M).Holds (v.storeAll (ringRemoveStores K (M.headD p) (M.getLastD p))) := by
  obtain ⟨hnd, hx⟩ := Links.slotFacts hws hS
  have hnd' := hnd
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons, not_or] at hnd'
  cases M with
  | nil => intro c hc; exact nomatch hc
  | cons m ms =>
    have hm := ring_writable hf (x := m) (by simp)
    cross m m
    rcases List.eq_nil_or_concat ms with rfl | ⟨mid, z, rfl⟩
    · simp only [ringRemoveStores, List.headD_cons, List.getLastD_nil, List.getLastD_cons]
      refine Frag.holds_update (f := []) hS (fun _ h => nomatch h) ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit m (by simp), fun i hi => (hm i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit m (by simp), fun i hi => (hm i hi).1, inSlotsFd (by simp)⟩
      · addr_ne
      · intro c hc
        simp only [ring, dseg, List.getLastD_nil, List.headD_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl <;> left <;> simp
    · simp only [List.concat_eq_append] at *
      simp only [ringRemoveStores, List.headD_cons, List.getLastD_cons, getLastD_concat]
      have hz := ring_writable hf (x := z) (by simp)
      cross m z; cross z m; cross z z; cross p m; cross m p; cross p z; cross z p
      have hmz : m ≠ z := by grind
      have hT : ∀ x ∈ mid, x ∈ p :: m :: (mid ++ [z]) ∧ (x ≠ m ∧ x ≠ z ∧
          x + K.fd ≠ m + K.bk ∧ m + K.fd ≠ x + K.bk ∧
          x + K.fd ≠ z + K.bk ∧ z + K.fd ≠ x + K.bk ∧ x + K.fd ≠ x + K.bk) := fun x hxt => by
        have hxN : x ∈ p :: m :: (mid ++ [z]) := by simp [hxt]
        exact ⟨hxN, by grind, by grind, hx x hxN m (by simp), hx m (by simp) x hxN,
          hx x hxN z (by simp), hx z (by simp) x hxN, hx x hxN x hxN⟩
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit z (by simp), fun i hi => (hm i hi).2, inSlotsBk (by simp)⟩
        · exact ⟨hfit m (by simp), fun i hi => (hz i hi).1, inSlotsFd (by simp)⟩
      · addr_ne
      · simp only [ring, List.append_assoc, List.cons_append, List.nil_append, dseg_append, dseg,
          List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, headD_append_cons,
          List.forall_mem_cons, List.forall_mem_append]
        refine ⟨by cell_tac, by cell_tac, by seg_tac hT, by cell_tac, by cell_tac, ?_⟩
        simp

end Silmaril.Data.SepList
