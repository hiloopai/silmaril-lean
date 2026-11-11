module

public import Silmaril.Games.Strategy.Thms
public import Silmaril.Games.Zip.Thms
public import Silmaril.Games.Div.Thms

/-!
# Interactions: positions and projections

* Positions along an interaction (`Compat`, `zip_path`). These are restated
  from `Silmaril.Proofs.Games.Composition.Legal` (same statements and proof),
  because the layout rules forbid importing another topic's proofs.
* Projections of an interaction: the visible events of each side and the
  synchronised events agree (`zip_lefts`, `zip_rights`, `zip_sync`).
* Who is running when a composite diverges: after a divergent play of one
  component (`run_of_div_left`, `run_of_div_right`) and after infinite hidden
  chatter (`run_of_chatter`), the composite is in a running position.
-/

public section

namespace Silmaril.Proofs.Games.DivComp

open Silmaril.Games

universe u v w

/-! ## Projections of interactions -/

section Proj

variable {α : Type u} {β : Type v} {γ : Type w}

theorem length_split : ∀ s : List (α ⊕ β),
    s.length = (s.filterMap Sum.getLeft?).length + (s.filterMap Sum.getRight?).length
  | [] => rfl
  | .inl _ :: s => by simp [List.filterMap_cons, length_split s]; omega
  | .inr _ :: s => by simp [List.filterMap_cons, length_split s]; omega

theorem zip_lefts {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.filterMap Sum.getLeft? = s.filterMap Sum.getLeft? := by
  induction h with
  | nil => rfl
  | left a _ ih => simp [ih]
  | right c _ ih => simpa [List.filterMap_cons] using ih
  | sync b _ ih => simpa [List.filterMap_cons] using ih

theorem zip_rights {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.filterMap Sum.getRight? = t.filterMap Sum.getRight? := by
  induction h with
  | nil => rfl
  | left a _ ih => simpa [List.filterMap_cons] using ih
  | right c _ ih => simp [ih]
  | sync b _ ih => simpa [List.filterMap_cons] using ih

theorem zip_sync {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    s.filterMap Sum.getRight? = t.filterMap Sum.getLeft? := by
  induction h with
  | nil => rfl
  | left a _ ih => simpa [List.filterMap_cons] using ih
  | right c _ ih => simpa [List.filterMap_cons] using ih
  | sync b _ ih => simp [ih]

/-- Visible length of an interaction. -/
theorem zip_length {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    p.length = (s.filterMap Sum.getLeft?).length + (t.filterMap Sum.getRight?).length := by
  rw [length_split p, zip_lefts h, zip_rights h]

theorem filterMap_left_nil_head {d : List (α ⊕ β)} (h : d.filterMap Sum.getLeft? = [])
    (hne : d ≠ []) : ∃ b d', d = .inr b :: d' := by
  match d, h with
  | .inr b :: d', _ => exact ⟨b, d', rfl⟩
  | [], _ => exact absurd rfl hne

theorem filterMap_right_nil_head {d : List (α ⊕ β)} (h : d.filterMap Sum.getRight? = [])
    (hne : d ≠ []) : ∃ a d', d = .inl a :: d' := by
  match d, h with
  | .inl a :: d', _ => exact ⟨a, d', rfl⟩
  | [], _ => exact absurd rfl hne

/-- Two lists with the same projections, one a near-prefix of the other, are
equal. -/
theorem eq_of_near {p s : List (α ⊕ β)}
    (hn : p <+: s ∨ ∃ p₀ o, p = p₀ ++ [o] ∧ p₀ <+: s)
    (hl : p.filterMap Sum.getLeft? = s.filterMap Sum.getLeft?)
    (hr : p.filterMap Sum.getRight? = s.filterMap Sum.getRight?) : p = s := by
  have hlen : p.length = s.length := by rw [length_split p, length_split s, hl, hr]
  rcases hn with h | ⟨p₀, o, rfl, h⟩
  · exact h.eq_of_length hlen
  · obtain ⟨d, rfl⟩ := h
    simp only [List.length_append, List.length_singleton, Nat.add_left_cancel_iff] at hlen
    obtain ⟨o', rfl⟩ := List.length_eq_one_iff.1 hlen.symm
    simp only [List.filterMap_append, List.append_cancel_left_eq] at hl hr
    congr 2
    rcases o with a | b <;> rcases o' with a' | b' <;> simp_all [List.filterMap_cons]

end Proj

/-! ## Positions along an interaction -/

variable {E F G : Sig.{u}}

/-- The reachable combinations of positions during an interaction (as in
`Silmaril.Proofs.Games.Composition.Legal`). -/
inductive Compat : Pos E F → Pos F G → Pos E G → Prop
  | idle : Compat .idle .idle .idle
  | run (g : G.Op) : Compat .idle (.run g) (.run g)
  | call (g : G.Op) (f : F.Op) : Compat (.run f) (.wait g f) (.run g)
  | wait (g : G.Op) (f : F.Op) (e : E.Op) : Compat (.wait f e) (.wait g f) (.wait g e)

theorem zip_path {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b t b' →
      ∃ c', Path c p c' ∧ Compat a' b' c' := by
  induction h with
  | nil =>
    intro a b c a' b' hc hs ht
    cases hs; cases ht
    exact ⟨c, .nil _, hc⟩
  | @left s t p x _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inl x :: s) a' → Path b t b' →
      ∃ c', Path c (.inl x :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hst hs =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.wait _ _ _) hs ht
        exact ⟨c', .cons (.call _ _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.call _ _) hs ht
        exact ⟨c', .cons (.reply _ _ _) hp, hc'⟩
  | @right s t p y _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a s a' → Path b (.inr y :: t) b' →
      ∃ c', Path c (.inr y :: p) c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases ht with
    | cons hst ht =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (Compat.run _) hs ht
        exact ⟨c', .cons (.ask _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih Compat.idle hs ht
        exact ⟨c', .cons (.ret _ _) hp, hc'⟩
  | @sync s t p z _ ih =>
    show ∀ {a b c a' b'}, Compat a b c → Path a (.inr z :: s) a' → Path b (.inl z :: t) b' →
      ∃ c', Path c p c' ∧ Compat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hs₁ hs =>
      cases ht with
      | cons ht₁ ht =>
        cases hs₁ <;> cases ht₁ <;> cases hc
        · exact ih (Compat.call _ _) hs ht
        · exact ih (Compat.run _) hs ht

/-- After a divergent (running) play of the lower component, the composite is
running. -/
theorem run_of_div_left {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) {f : F.Op} (hs : Path .idle s (.run f)) (ht : Legal t) :
    ∃ g, Path .idle p (.run g) := by
  obtain ⟨b, ht⟩ := ht
  obtain ⟨c, hp, hc⟩ := zip_path h Compat.idle hs ht
  cases hc
  exact ⟨_, hp⟩

/-- After a divergent (running) play of the upper component, the composite is
running. -/
theorem run_of_div_right {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) (hs : Legal s) {g : G.Op} (ht : Path .idle t (.run g)) :
    ∃ g, Path .idle p (.run g) := by
  obtain ⟨a, hs⟩ := hs
  obtain ⟨c, hp, hc⟩ := zip_path h Compat.idle hs ht
  cases hc
  exact ⟨_, hp⟩

private theorem no_step_idle_inl {o : Ev E} {y : Pos E F} (h : Step .idle (.inl o) y) : False := by
  cases h

private theorem no_step_wait_inr {q : F.Op} {m : E.Op} {o : Ev F} {y : Pos E F}
    (h : Step (.wait q m) (.inr o) y) : False := by
  cases h

/-- The extensions of two interactions with the same visible part are hidden
synchronisations. -/
private theorem hidden_ext {s₀ d : List (Move E F)} {t₀ e : List (Move F G)} {p : List (Move E G)}
    (h₀ : Zip s₀ t₀ p) (h₁ : Zip (s₀ ++ d) (t₀ ++ e) p) :
    d.filterMap Sum.getLeft? = [] ∧ e.filterMap Sum.getRight? = [] ∧
      d.filterMap Sum.getRight? = e.filterMap Sum.getLeft? := by
  have l₀ : _ = _ := zip_lefts h₀
  have l₁ : _ = _ := zip_lefts h₁
  have r₀ : _ = _ := zip_rights h₀
  have r₁ : _ = _ := zip_rights h₁
  have y₀ : _ = _ := zip_sync h₀
  have y₁ : _ = _ := zip_sync h₁
  simp only [List.filterMap_append] at l₁ r₁ y₁
  rw [l₀] at l₁
  rw [r₀] at r₁
  rw [y₀] at y₁
  exact ⟨by simpa using l₁, by simpa using r₁, List.append_cancel_left y₁⟩

private theorem length_eq_of_hidden {d : List (Move E F)} {e : List (Move F G)}
    (hld : d.filterMap Sum.getLeft? = []) (hre : e.filterMap Sum.getRight? = [])
    (hsy : d.filterMap Sum.getRight? = e.filterMap Sum.getLeft?) : d.length = e.length := by
  rw [length_split d, length_split e, hld, hre, hsy]
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero]

private theorem tail_path {x a : Pos E F} {s d : List (Move E F)} (h₀ : Path x s a)
    (h : ∃ z, Path x (s ++ d) z) : ∃ y, Path a d y := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨a', h₁, h₂⟩ := Path.of_append hz
  exact ⟨z, (h₀.det h₁) ▸ h₂⟩

private theorem run_of_compat {a : Pos E F} {b : Pos F G} {c : Pos E G} {p : List (Move E G)}
    {x : Ev F} {d : List (Move E F)} {y : Ev F} {e : List (Move F G)} (hc : Compat a b c)
    (hpc : Path .idle p c) (hd : ∃ z, Path a (.inr x :: d) z) (he : ∃ z, Path b (.inl y :: e) z) :
    ∃ g, Path .idle p (.run g) := by
  cases hc with
  | idle => obtain ⟨_, hz⟩ := he; cases hz with | cons st _ => exact (no_step_idle_inl st).elim
  | run g => exact ⟨g, hpc⟩
  | call g f => exact ⟨g, hpc⟩
  | wait g f e => obtain ⟨_, hz⟩ := hd; cases hz with | cons st _ => exact (no_step_wait_inr st).elim

/-- **Infinite hidden chatter happens in a running position.** If a sequence
of increasing interactions of legal plays keeps the same visible play `p` while
the hidden part grows, `p` ends in a running position. -/
theorem run_of_chatter {s : Chain (Move E F)} {t : Chain (Move F G)} {p : List (Move E G)}
    (hz : ∀ n, Zip (s n) (t n) p) (hs : ∀ n, Legal (s n)) (ht : ∀ n, Legal (t n))
    (hms : s.Mono) (hmt : t.Mono)
    (hu : ∀ k, ∃ n, k ≤ (s n).length + (t n).length) : ∃ g, Path .idle p (.run g) := by
  obtain ⟨m, hm⟩ : ∃ m, (s 0).length + (t 0).length + 1 ≤ (s m).length + (t m).length := hu _
  obtain ⟨d, hd⟩ : ∃ d, s 0 ++ d = s m := hms.le (Nat.zero_le m)
  obtain ⟨e, he⟩ : ∃ e, t 0 ++ e = t m := hmt.le (Nat.zero_le m)
  have hzm : Zip (s 0 ++ d) (t 0 ++ e) p := by rw [hd, he]; exact hz m
  obtain ⟨hld, hre, hsy⟩ := hidden_ext (hz 0) hzm
  have hlen : d.length = e.length := length_eq_of_hidden hld hre hsy
  have hsl : (s m).length = (s 0).length + d.length := by rw [← hd, List.length_append]
  have htl : (t m).length = (t 0).length + e.length := by rw [← he, List.length_append]
  have hd0 : d ≠ [] := List.ne_nil_of_length_pos (by omega)
  have he0 : e ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨b, d', hd'⟩ : ∃ b d', d = .inr b :: d' := filterMap_left_nil_head hld hd0
  obtain ⟨a, e', he'⟩ : ∃ a e', e = .inl a :: e' := filterMap_right_nil_head hre he0
  obtain ⟨a₀, ps₀⟩ : ∃ a₀, Path .idle (s 0) a₀ := hs 0
  obtain ⟨b₀, pt₀⟩ : ∃ b₀, Path .idle (t 0) b₀ := ht 0
  obtain ⟨c, hpc, hc⟩ : ∃ c, Path .idle p c ∧ Compat a₀ b₀ c := zip_path (hz 0) Compat.idle ps₀ pt₀
  have psd : ∃ y, Path a₀ d y := tail_path ps₀ (hd ▸ hs m)
  have pte : ∃ y, Path b₀ e y := tail_path pt₀ (he ▸ ht m)
  exact run_of_compat hc hpc (hd' ▸ psd) (he' ▸ pte)

end Silmaril.Proofs.Games.DivComp
