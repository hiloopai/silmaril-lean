module

public import Silmaril.Proofs.Data.SepList.Basic

/-!
# Doubly linked lists with a sentinel: push front and unlink
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Silmaril.Data.SepList

open Silmaril.Data

theorem inSlotsFd {K : Links} {N : List Nat} {x : Nat} (hx : x ∈ N) :
    ∃ e ∈ K.slots N, e.addr = x + K.fd ∧ e.width = K.ws :=
  inSlots (c := ⟨x + K.fd, K.ws, 0⟩) hx rfl (.inl rfl)

theorem inSlotsBk {K : Links} {N : List Nat} {x : Nat} (hx : x ∈ N) :
    ∃ e ∈ K.slots N, e.addr = x + K.bk ∧ e.width = K.ws :=
  inSlots (c := ⟨x + K.bk, K.ws, 0⟩) hx rfl (.inr rfl)

theorem getLastD_concat (l : List Nat) (x d : Nat) : (l ++ [x]).getLastD d = x := by
  simp [List.getLastD_eq_getLast?]

theorem getLastD_append_cons {x d : Nat} {xs : List Nat} :
    ∀ (l : List Nat), (l ++ x :: xs).getLastD d = xs.getLastD x
  | [] => List.getLastD_cons
  | y :: ys => by rw [List.cons_append, List.getLastD_cons, getLastD_append_cons ys]

/-- Address goals: unfold the store addresses and decide by `omega` from the slot facts in
context. -/
macro "addr_ne" : tactic =>
  `(tactic| (simp only [List.map_cons, List.map_nil, List.headD_nil, List.mem_cons, List.not_mem_nil, or_false,
               not_or, not_false_eq_true, and_true, List.nodup_cons, List.nodup_nil];
             omega))

/-- Membership of a cell in an unfolded list fragment. -/
macro "mem_frag" : tactic =>
  `(tactic| (simp only [dll, dseg, ring, List.append_assoc, List.cons_append, List.nil_append,
               dseg_append, List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, getLastD_append_cons,
               headD_append_cons, List.getLastD_nil, List.mem_cons, List.mem_append, true_or, or_true]))

/-- `mem_frag` with one extra membership fact. -/
macro "mem_frag_with" h:term : tactic =>
  `(tactic| (simp only [dll, dseg, ring, List.append_assoc, List.cons_append, List.nil_append,
               dseg_append, List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, getLastD_append_cons,
               headD_append_cons, List.getLastD_nil, List.mem_cons, List.mem_append, true_or, or_true, $h:term]))

theorem dllPushFront : Task.seplist.dllPushFront := by
  intro K v s a l hws hf hS hfit hwa
  obtain ⟨hnd, hx⟩ := Links.slotFacts hws hS
  have fa : a < 256 ^ K.ws := hfit a (by simp)
  have fs : s < 256 ^ K.ws := hfit s (by simp)
  have hxas := hx a (by simp) s (by simp)
  have hxsa := hx s (by simp) a (by simp)
  have hxaa := hx a (by simp) a (by simp)
  have hxss := hx s (by simp) s (by simp)
  have has : a ≠ s := fun e => (List.nodup_cons.1 hnd).1 (by simp [e])
  cases l with
  | nil =>
    simp only [List.headD_nil]
    refine Frag.holds_update hS hf ?_ ?_ ?_
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨fs, fun i hi => (hwa i hi).1, inSlots (x := a) (by simp) rfl (.inl rfl)⟩
      · exact ⟨fs, fun i hi => (hwa i hi).2, inSlots (x := a) (by simp) rfl (.inr rfl)⟩
      · exact ⟨fa, fun i hi => (hf ⟨s + K.fd, K.ws, s⟩ (by mem_frag) |>.2 i hi), inSlots (x := s) (by simp) rfl (.inl rfl)⟩
      · exact ⟨fa, fun i hi => (hf ⟨s + K.bk, K.ws, s⟩ (by mem_frag) |>.2 i hi), inSlots (x := s) (by simp) rfl (.inr rfl)⟩
    · addr_ne
    · intro c hc
      left
      simp only [dll, dseg, List.headD_cons, List.headD_nil, List.getLastD_cons, List.getLastD_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> simp
  | cons h t =>
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd'
    obtain ⟨⟨_, hah, hat⟩, ⟨hsh, hst⟩, hht, _⟩ := hnd'
    have hxah := hx a (by simp) h (by simp)
    have hxha := hx h (by simp) a (by simp)
    have hxsh := hx s (by simp) h (by simp)
    have hxhs := hx h (by simp) s (by simp)
    have hxhh := hx h (by simp) h (by simp)
    have fh : h < 256 ^ K.ws := hfit h (by simp)
    simp only [List.headD_cons]
    refine Frag.holds_update hS hf ?_ ?_ ?_
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · exact ⟨fh, fun i hi => (hwa i hi).1, inSlots (x := a) (by simp) rfl (.inl rfl)⟩
      · exact ⟨fs, fun i hi => (hwa i hi).2, inSlots (x := a) (by simp) rfl (.inr rfl)⟩
      · exact ⟨fa, fun i hi => (hf ⟨s + K.fd, K.ws, h⟩ (by mem_frag) |>.2 i hi), inSlots (x := s) (by simp) rfl (.inl rfl)⟩
      · exact ⟨fa, fun i hi => (hf ⟨h + K.bk, K.ws, s⟩ (by mem_frag) |>.2 i hi),
          inSlots (x := h) (by simp) rfl (.inr rfl)⟩
    · addr_ne
    · intro c hc
      simp only [dll, dseg, List.headD_cons, List.getLastD_cons, List.mem_cons] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hc
      · left; simp
      · right
        refine ⟨by mem_frag, inSlots (x := s) (by simp) rfl (.inr rfl), ?_⟩
        addr_ne
      · left; simp
      · left; simp
      · right
        refine ⟨by mem_frag, inSlots (x := h) (by simp) rfl (.inl rfl), ?_⟩
        addr_ne
      · left; simp
      · obtain ⟨x, hxt, hw, ha⟩ := mem_dseg hc
        have hxa : x ≠ a := fun e => hat (e ▸ hxt)
        have hxs : x ≠ s := fun e => hst (e ▸ hxt)
        have hxh : x ≠ h := fun e => hht (e ▸ hxt)
        have h1 := hx x (by simp [hxt]) a (by simp)
        have h2 := hx a (by simp) x (by simp [hxt])
        have h3 := hx x (by simp [hxt]) s (by simp)
        have h4 := hx s (by simp) x (by simp [hxt])
        have h5 := hx x (by simp [hxt]) h (by simp)
        have h6 := hx h (by simp) x (by simp [hxt])
        right
        refine ⟨by mem_frag_with hc, inSlots (x := x) (by simp [hxt]) hw ha, ?_⟩
        rcases ha with ha | ha <;> rw [ha] <;> addr_ne

/-- A retained old cell: in the old fragment, in a slot, at no stored address. -/
macro "old_cell" : tactic =>
  `(tactic| (right; refine ⟨by mem_frag, ?_, by addr_ne⟩;
             first | (apply inSlotsFd; simp; done) | (apply inSlotsBk; simp)))

/-- A cell of the new fragment: a store, or a retained old cell. -/
macro "cell_tac" : tactic => `(tactic| first | (left; simp; done) | old_cell)

/-- The cells of a shared segment: retained, given `hT x hx` (slot membership, and the address
facts for `omega`) for its nodes. -/
macro "seg_tac" hT:term:max : tactic =>
  `(tactic| (intro c hc; obtain ⟨x, hxt, hw, ha⟩ := mem_dseg hc; right;
             obtain ⟨hxN, hfx⟩ := $hT x hxt;
             refine ⟨by mem_frag_with hc, inSlots hxN hw ha, ?_⟩;
             rcases ha with ha | ha <;> rw [ha] <;> addr_ne))

/-- Instantiate the cross fact `x + fd ≠ y + bk` for two named nodes. -/
macro "cross" x:term:max y:term:max : tactic =>
  `(tactic| have := $(Lean.mkIdent `hx) $x (by simp) $y (by simp))

theorem dllUnlink : Task.seplist.dllUnlink := by
  intro K v s a l₁ l₂ hws hf hS hfit
  obtain ⟨hnd, hx⟩ := Links.slotFacts hws hS
  rcases List.eq_nil_or_concat l₁ with rfl | ⟨init, P, rfl⟩
  all_goals try simp only [List.concat_eq_append] at *
  all_goals have hnd' := hnd
  all_goals simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
    not_or] at hnd'
  · cases l₂ with
    | nil =>
      -- l₁ = [], l₂ = []
      simp only [List.headD_nil, List.getLastD_nil]
      cross s s
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit s (by simp), fun i hi => (hf ⟨s + K.bk, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := s) (by simp) rfl (.inr rfl)⟩
        · exact ⟨hfit s (by simp), fun i hi => (hf ⟨s + K.fd, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := s) (by simp) rfl (.inl rfl)⟩
      · addr_ne
      · intro c hc
        simp only [dll, dseg, List.nil_append, List.headD_nil, List.getLastD_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> left <;> simp
    | cons h t =>
      -- l₁ = [], l₂ = h :: t
      simp only [List.headD_cons, List.getLastD_nil, List.nil_append]
      cross s s; cross s h; cross h s; cross h h
      have hsh : s ≠ h := by grind
      have hT : ∀ x ∈ t, x ∈ s :: ([] ++ a :: h :: t) ∧ (x ≠ s ∧ x ≠ h ∧
          x + K.fd ≠ s + K.bk ∧ s + K.fd ≠ x + K.bk ∧ x + K.fd ≠ h + K.bk ∧ h + K.fd ≠ x + K.bk ∧
          x + K.fd ≠ x + K.bk) := fun x hxt =>
        ⟨by simp [hxt], by grind, by grind, hx x (by simp [hxt]) s (by simp),
          hx s (by simp) x (by simp [hxt]), hx x (by simp [hxt]) h (by simp),
          hx h (by simp) x (by simp [hxt]), hx x (by simp [hxt]) x (by simp [hxt])⟩
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit s (by simp), fun i hi => (hf ⟨h + K.bk, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := h) (by simp) rfl (.inr rfl)⟩
        · exact ⟨hfit h (by simp), fun i hi => (hf ⟨s + K.fd, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := s) (by simp) rfl (.inl rfl)⟩
      · addr_ne
      · simp only [dll, dseg, List.nil_append, List.headD_cons, List.getLastD_cons,
          List.forall_mem_cons]
        refine ⟨by cell_tac, by cell_tac, by cell_tac, by cell_tac, by seg_tac hT⟩
  · cases l₂ with
    | nil =>
      -- l₁ = init ++ [P], l₂ = []
      simp only [List.headD_nil, getLastD_concat]
      cross s s; cross s P; cross P s; cross P P
      have hsP : s ≠ P := by grind
      have hT : ∀ x ∈ init, x ∈ s :: (init ++ [P, a]) ∧ (x ≠ s ∧ x ≠ P ∧
          x + K.fd ≠ s + K.bk ∧ s + K.fd ≠ x + K.bk ∧ x + K.fd ≠ P + K.bk ∧ P + K.fd ≠ x + K.bk ∧
          x + K.fd ≠ x + K.bk) := fun x hxt =>
        ⟨by simp [hxt], by grind, by grind, hx x (by simp [hxt]) s (by simp),
          hx s (by simp) x (by simp [hxt]), hx x (by simp [hxt]) P (by simp),
          hx P (by simp) x (by simp [hxt]), hx x (by simp [hxt]) x (by simp [hxt])⟩
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit P (by simp), fun i hi => (hf ⟨s + K.bk, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := s) (by simp) rfl (.inr rfl)⟩
        · exact ⟨hfit s (by simp), fun i hi => (hf ⟨P + K.fd, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := P) (by simp) rfl (.inl rfl)⟩
      · addr_ne
      · simp only [dll, List.append_assoc, List.cons_append, List.nil_append, dseg_append, dseg,
          List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, getLastD_append_cons, headD_append_cons,
          List.forall_mem_cons, List.forall_mem_append]
        refine ⟨by cell_tac, by cell_tac, by seg_tac hT, by cell_tac, by cell_tac, ?_⟩
        simp
    | cons h t =>
      -- l₁ = init ++ [P], l₂ = h :: t
      simp only [List.headD_cons, getLastD_concat]
      cross s s; cross s P; cross P s; cross P P; cross s h; cross h s; cross h h; cross P h
      cross h P
      have hsP : s ≠ P := by grind
      have hsh : s ≠ h := by grind
      have hPh : P ≠ h := by grind
      have hT : ∀ x ∈ init ++ t, x ∈ s :: (init ++ P :: a :: h :: t) ∧ (x ≠ s ∧ x ≠ P ∧ x ≠ h ∧
          x + K.fd ≠ s + K.bk ∧ s + K.fd ≠ x + K.bk ∧ x + K.fd ≠ P + K.bk ∧ P + K.fd ≠ x + K.bk ∧
          x + K.fd ≠ h + K.bk ∧ h + K.fd ≠ x + K.bk ∧ x + K.fd ≠ x + K.bk) := fun x hxt => by
        have hxN : x ∈ s :: (init ++ [P] ++ a :: h :: t) := by grind
        exact ⟨by simpa using hxN, by grind, by grind, by grind, hx x hxN s (by simp), hx s (by simp) x hxN,
          hx x hxN P (by simp), hx P (by simp) x hxN, hx x hxN h (by simp), hx h (by simp) x hxN,
          hx x hxN x hxN⟩
      have hTi : ∀ x ∈ init, _ := fun x hxt => hT x (List.mem_append_left _ hxt)
      have hTt : ∀ x ∈ t, _ := fun x hxt => hT x (List.mem_append_right _ hxt)
      refine Frag.holds_update hS hf ?_ ?_ ?_
      · intro d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact ⟨hfit P (by simp), fun i hi => (hf ⟨h + K.bk, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := h) (by simp) rfl (.inr rfl)⟩
        · exact ⟨hfit h (by simp), fun i hi => (hf ⟨P + K.fd, K.ws, a⟩ (by mem_frag)).2 i hi,
            inSlots (x := P) (by simp) rfl (.inl rfl)⟩
      · addr_ne
      · simp only [dll, List.append_assoc, List.cons_append, List.nil_append, dseg_append, dseg,
          List.headD_cons, List.headD_nil, List.getLastD_cons, getLastD_concat, getLastD_append_cons, headD_append_cons,
          List.forall_mem_cons, List.forall_mem_append]
        refine ⟨by cell_tac, by cell_tac, by seg_tac hTi, by cell_tac, by cell_tac, by cell_tac,
          by cell_tac, by seg_tac hTt⟩

end Silmaril.Data.SepList
