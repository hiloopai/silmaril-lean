module

public import Silmaril.Data.SepList.Defs
public import Silmaril.Data.Cells.Thms

/-!
# List segments: shape lemmas and the slot facts

`dseg` splits along `++`; its cells sit in the nodes' slots; a separated slot fragment gives
distinct nodes and distinct link fields (`Links.slotFacts`). Every list lemma uses these and
`Silmaril.Data.Frag.holds_update`.
-/

@[expose] public section

namespace Silmaril.Data.SepList

open Silmaril.Data

theorem headD_append_cons {l₂ : List Nat} {n : Nat} :
    ∀ (xs : List Nat), (xs ++ l₂).headD n = xs.headD (l₂.headD n)
  | [] => rfl
  | _ :: _ => rfl

theorem dseg_append (K : Links) :
    ∀ (p : Nat) (l₁ l₂ : List Nat) (n : Nat),
      dseg K p (l₁ ++ l₂) n = dseg K p l₁ (l₂.headD n) ++ dseg K (l₁.getLastD p) l₂ n
  | _, [], _, _ => rfl
  | p, x :: xs, l₂, n => by
    simp only [List.cons_append, dseg, headD_append_cons, List.getLastD_cons]
    rw [dseg_append K x xs l₂ n]

theorem dseg_concat (K : Links) (p : Nat) (l : List Nat) (x n : Nat) :
    dseg K p (l ++ [x]) n = dseg K p l x ++ [⟨x + K.fd, K.ws, n⟩, ⟨x + K.bk, K.ws, l.getLastD p⟩] := by
  rw [dseg_append]; rfl

theorem mem_dseg {K : Links} {c : Cell} : ∀ {p n : Nat} {l : List Nat}, c ∈ dseg K p l n →
    ∃ x ∈ l, c.width = K.ws ∧ (c.addr = x + K.fd ∨ c.addr = x + K.bk)
  | _, _, [], h => nomatch h
  | _, _, x :: xs, h => by
    simp only [dseg, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨x, List.mem_cons_self .., rfl, .inl rfl⟩
    · exact ⟨x, List.mem_cons_self .., rfl, .inr rfl⟩
    · obtain ⟨y, hy, hw, ha⟩ := mem_dseg h
      exact ⟨y, List.mem_cons_of_mem _ hy, hw, ha⟩

theorem slots_cons (K : Links) (x : Nat) (N : List Nat) :
    K.slots (x :: N) = K.node x 0 0 ++ K.slots N := rfl

theorem slots_append (K : Links) (N M : List Nat) :
    K.slots (N ++ M) = K.slots N ++ K.slots M := by
  simp [Links.slots]

/-- A cell of width `K.ws` at a link field of a node of `N` is in a slot of `N`. -/
theorem inSlots {K : Links} {N : List Nat} {c : Cell} {x : Nat} (hx : x ∈ N)
    (hw : c.width = K.ws) (ha : c.addr = x + K.fd ∨ c.addr = x + K.bk) :
    ∃ e ∈ K.slots N, e.addr = c.addr ∧ e.width = c.width := by
  rcases ha with ha | ha
  · exact ⟨⟨x + K.fd, K.ws, 0⟩, List.mem_flatMap.2 ⟨x, hx, by simp [Links.node]⟩, ha.symm, hw.symm⟩
  · exact ⟨⟨x + K.bk, K.ws, 0⟩, List.mem_flatMap.2 ⟨x, hx, by simp [Links.node]⟩, ha.symm, hw.symm⟩

theorem nodup_flatMap_pair {f g : Nat → Nat} : ∀ {N : List Nat},
    (N.flatMap fun x => [f x, g x]).Nodup → N.Nodup ∧ ∀ x ∈ N, ∀ y ∈ N, f x ≠ g y
  | [], _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | x :: xs, h => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := nodup_flatMap_pair h3
    refine ⟨List.nodup_cons.2 ⟨fun hx => h2 ⟨x, hx, by simp⟩, ih1⟩, ?_⟩
    intro u hu w hw
    rcases List.mem_cons.1 hu with hu' | hu' <;> rcases List.mem_cons.1 hw with hw' | hw'
    · rw [hu', hw']; exact fun e => h1 (.inl e)
    · rw [hu']; exact fun e => h1 (.inr ⟨w, hw', by simp [e]⟩)
    · rw [hw']; exact fun e => h2 ⟨u, hu', by simp [e]⟩
    · exact ih2 u hu' w hw'

/-- **The slot facts**: separated slots of width > 0 have distinct nodes, and no node's `fd`
field is another's (or its own) `bk` field. -/
theorem Links.slotFacts {K : Links} {N : List Nat} (hws : 0 < K.ws) (h : (K.slots N).Sep) :
    N.Nodup ∧ ∀ x ∈ N, ∀ y ∈ N, x + K.fd ≠ y + K.bk := by
  have := h.addrs_nodup fun c hc => by
    obtain ⟨x, _, hc⟩ := List.mem_flatMap.1 hc
    simp only [Links.node, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact hws
  have e : (K.slots N).map Cell.addr = N.flatMap fun x => [x + K.fd, x + K.bk] := by
    simp [Links.slots, Links.node, List.map_flatMap]
  rw [e] at this
  exact nodup_flatMap_pair this

theorem sublist_flatMap {α β : Type} {f : α → List β} : ∀ {l₁ l₂ : List α},
    l₁.Sublist l₂ → (l₁.flatMap f).Sublist (l₂.flatMap f)
  | _, _, .slnil => .slnil
  | _, _, .cons a h => by
    simp only [List.flatMap_cons]; exact (sublist_flatMap h).trans (List.sublist_append_right _ _)
  | _, _, .cons_cons a h => by
    simp only [List.flatMap_cons]; exact List.Sublist.append (List.Sublist.refl _) (sublist_flatMap h)

theorem Links.slots_sep_sub {K : Links} {N M : List Nat} (h : (K.slots N).Sep)
    (hs : M.Sublist N) : (K.slots M).Sep :=
  List.Nodup.sublist (by
    unfold Frag.bytes Links.slots
    exact sublist_flatMap (sublist_flatMap hs)) h

end Silmaril.Data.SepList
