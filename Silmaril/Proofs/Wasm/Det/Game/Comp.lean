module

public import Silmaril.Proofs.Wasm.Det.Game.Inter

/-!
# Composition preserves determinism and statelessness modulo traps

Two interactions whose visible plays are `p ++ [m₁]` and `p ++ [m₂]` are compared at the first
letter where they differ (`lcp`). The coherent positions there (`Coh`) say who moves:

* Opponent: both letters are visible Opponent moves, so they lie in `p` and are equal;
* `τ`: `τ`'s determinism applies, since `τ`'s traps are visible and `p` is trap-free;
* `σ`: `σ`'s determinism applies once `σ`'s play so far is trap-free. A hidden trap of `σ` is
  followed by a visible trap of `τ` (`after_trap`, from strictness of `τ`), which cannot lie in
  `p`; a hidden trap at the point of divergence makes `m₁` a trap (`hidden_trap`).

The same argument after histories that end idle gives statelessness (`agree_comp`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F G : Sig.{u}}

/-! ## Lists -/

/-- Two lists are comparable or differ at a first position. -/
theorem lcp {α : Type*} : ∀ w₁ w₂ : List α, w₁ <+: w₂ ∨ w₂ <+: w₁ ∨
    ∃ u x₁ x₂ r₁ r₂, x₁ ≠ x₂ ∧ w₁ = u ++ x₁ :: r₁ ∧ w₂ = u ++ x₂ :: r₂
  | [], _ => .inl List.nil_prefix
  | _ :: _, [] => .inr (.inl List.nil_prefix)
  | x₁ :: w₁, x₂ :: w₂ => by
    by_cases hx : x₁ = x₂
    · subst hx
      rcases lcp w₁ w₂ with h | h | ⟨u, y₁, y₂, r₁, r₂, hne, rfl, rfl⟩
      · exact .inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
      · exact .inr (.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩))
      · exact .inr (.inr ⟨x₁ :: u, y₁, y₂, r₁, r₂, hne, rfl, rfl⟩)
    · exact .inr (.inr ⟨[], x₁, x₂, w₁, w₂, hx, rfl, rfl⟩)

theorem eq_of_concat_prefix {α : Type*} {p : List α} {m₁ m₂ : α}
    (h : p ++ [m₁] <+: p ++ [m₂]) : m₁ = m₂ := by
  have h' := h.eq_of_length (by simp)
  simpa using h'

theorem next_vis {α : Type*} {a p : List α} {o m : α} (h : a ++ [o] <+: p ++ [m]) :
    a ++ [o] <+: p ∨ (a = p ∧ o = m) := by
  rcases List.prefix_concat_iff.1 h with h | h
  · exact .inr (by simpa using List.append_inj' h rfl)
  · exact .inl h

theorem prefix_same {α : Type*} {a p : List α} {o₁ o₂ : α} (h₁ : a ++ [o₁] <+: p)
    (h₂ : a ++ [o₂] <+: p) : o₁ = o₂ := by
  obtain ⟨k₁, rfl⟩ := h₁
  obtain ⟨k₂, h⟩ := h₂
  simp only [List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
    List.cons.injEq] at h
  exact h.1.symm

/-! ## Positions and prefixes -/

theorem path_after {E F : Sig.{u}} {σ : Strategy E F} {H Y : List (Move E F)}
    (hH : Path .idle H .idle) (hm : H ++ Y ∈ σ) : ∃ x, Path .idle Y x := by
  obtain ⟨y, hy⟩ := σ.legal hm
  obtain ⟨y₀, h₀, h₁⟩ := Path.of_append hy
  rw [Path.det h₀ hH] at h₁
  exact ⟨y, h₁⟩

theorem step_after {E F : Sig.{u}} {σ : Strategy E F} {H Y : List (Move E F)} {z : Move E F}
    {x : Pos E F} (hH : Path .idle H .idle) (hY : Path .idle Y x) (hm : H ++ (Y ++ [z]) ∈ σ) :
    ∃ x', Step x z x' := by
  obtain ⟨y, hy⟩ := path_after hH hm
  obtain ⟨y₂, h₂, h₃⟩ := Path.concat_iff.1 hy
  rw [Path.det h₂ hY] at h₃
  exact ⟨y, h₃⟩

theorem mem_pre_L {σ : Strategy E F} {H : List (Move E F)} {u w : List (Letter E F G)}
    (h : H ++ L w ∈ σ) (hu : u <+: w) : H ++ L u ∈ σ :=
  σ.of_prefix h ((List.prefix_append_right_inj H).2 (hu.filterMap lv))

theorem mem_pre_R {τ : Strategy F G} {K : List (Move F G)} {u w : List (Letter E F G)}
    (h : K ++ R w ∈ τ) (hu : u <+: w) : K ++ R u ∈ τ :=
  τ.of_prefix h ((List.prefix_append_right_inj K).2 (hu.filterMap rv))

/-! ## Whose turn -/

theorem turn_o_idle {x : Letter E F G}
    (hl : ∀ z, lv x = some z → ∃ x', Step (.idle : Pos E F) z x')
    (hr : ∀ y, rv x = some y → ∃ y', Step (.idle : Pos F G) y y') :
    ∃ o, vv x = some o ∧ o.IsO := by
  rcases x with a | b | (q | ⟨q, r⟩)
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · obtain ⟨_, h⟩ := hr _ rfl
    cases h
  · exact ⟨_, rfl, trivial⟩
  · obtain ⟨_, h⟩ := hr _ rfl
    cases h

theorem turn_o_wait {x : Letter E F G} {q : G.Op} {m : F.Op} {e : E.Op}
    (hl : ∀ z, lv x = some z → ∃ x', Step (.wait m e : Pos E F) z x')
    (hr : ∀ y, rv x = some y → ∃ y', Step (.wait q m : Pos F G) y y') :
    ∃ o, vv x = some o ∧ o.IsO := by
  rcases x with (a | ⟨a, n⟩) | b | c
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · exact ⟨_, rfl, trivial⟩
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · obtain ⟨_, h⟩ := hr _ rfl
    cases h

theorem turn_t {x : Letter E F G} {q : G.Op}
    (hl : ∀ z, lv x = some z → ∃ x', Step (.idle : Pos E F) z x')
    (hr : ∀ y, rv x = some y → ∃ y', Step (.run q : Pos F G) y y') :
    ∃ y, rv x = some y ∧ y.IsP := by
  rcases x with a | (b | ⟨b, n⟩) | (c | ⟨c, r⟩)
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · exact ⟨_, rfl, trivial⟩
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · obtain ⟨_, h⟩ := hr _ rfl
    cases h
  · exact ⟨_, rfl, trivial⟩

theorem turn_s {x : Letter E F G} {q : G.Op} {m : F.Op}
    (hl : ∀ z, lv x = some z → ∃ x', Step (.run m : Pos E F) z x')
    (hr : ∀ y, rv x = some y → ∃ y', Step (.wait q m : Pos F G) y y') :
    ∃ z, lv x = some z ∧ z.IsP := by
  rcases x with (a | ⟨a, n⟩) | (b | ⟨b, n⟩) | c
  · exact ⟨_, rfl, trivial⟩
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · obtain ⟨_, h⟩ := hl _ rfl
    cases h
  · exact ⟨_, rfl, trivial⟩
  · obtain ⟨_, h⟩ := hr _ rfl
    cases h

/-! ## Traps -/

/-- **After a hidden trap of `σ`, the next letter is a visible trap of `τ`** (strictness). -/
theorem after_trap {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    (hst : Strict tF tG τ) {H : List (Move E F)} {K : List (Move F G)}
    {u : List (Letter E F G)} {m : F.Op} {n : F.Ar m} (htr : tF m n) {x : Letter E F G}
    (hs : H ++ L (u ++ [.inr (.inl (.ans m n)), x]) ∈ σ)
    (ht : K ++ R (u ++ [.inr (.inl (.ans m n)), x]) ∈ τ) :
    ∃ q v, x = .inr (.inr (.ans q v)) ∧ tG q v := by
  rcases x with a | b | (c | ⟨q, v⟩)
  · exfalso
    obtain ⟨y, hy⟩ := σ.legal hs
    have he : H ++ L (u ++ [.inr (.inl (.ans m n)), .inl a]) =
        (H ++ L u ++ [.inr (.ans m n)]) ++ [.inl a] := by simp [lv]
    rw [he] at hy
    obtain ⟨y₁, h₁, h₂⟩ := Path.concat_iff.1 hy
    obtain ⟨y₀, -, h₃⟩ := Path.concat_iff.1 h₁
    cases h₃
    cases h₂
  · exact (hst (K ++ R u) m n (.inl b) (by simpa [rv] using ht) htr).elim
  · exact (hst (K ++ R u) m n (.inr (.ask c)) (by simpa [rv] using ht) htr).elim
  · exact ⟨q, v, rfl, hst (K ++ R u) m n (.inr (.ans q v)) (by simpa [rv] using ht) htr⟩

/-- A hidden trap of `σ` right after the common part `u` makes the next visible move a
trap. -/
theorem hidden_trap {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    (hst : Strict tF tG τ) {H : List (Move E F)} {K : List (Move F G)}
    {u r : List (Letter E F G)} {m : F.Op} {n : F.Ar m} (htr : tF m n)
    {p : List (Move E G)} {m₁ : Move E G}
    (hs : H ++ L (u ++ .inr (.inl (.ans m n)) :: r) ∈ σ)
    (ht : K ++ R (u ++ .inr (.inl (.ans m n)) :: r) ∈ τ)
    (hv : V (u ++ .inr (.inl (.ans m n)) :: r) = p ++ [m₁]) (hVu : V u <+: p)
    (hp : TrapFree tG p) : PTrap tG m₁ := by
  cases r with
  | nil =>
    have h : V u = p ++ [m₁] := by simpa [vv] using hv
    have hl := hVu.length_le
    rw [h, List.length_append] at hl
    simp only [List.length_singleton] at hl
    omega
  | cons x r =>
    have hpre : u ++ [.inr (.inl (.ans m n)), x] <+: u ++ .inr (.inl (.ans m n)) :: x :: r :=
      ⟨r, by simp⟩
    obtain ⟨q, v, rfl, hqv⟩ := after_trap hst htr (mem_pre_L hs hpre) (mem_pre_R ht hpre)
    have hn : V u ++ [.inr (.ans q v)] <+: p ++ [m₁] := by
      rw [← hv]
      exact ⟨V r, by simp [vv]⟩
    rcases next_vis hn with h | ⟨-, rfl⟩
    · exact absurd hqv (hp (.inr (.ans q v)) (h.subset (by simp)))
    · exact hqv

/-- Two visible Opponent letters at the point of divergence are impossible. -/
theorem o_case {u : List (Letter E F G)} {x₁ x₂ : Letter E F G} {p : List (Move E G)}
    {m₁ m₂ o₁ o₂ : Move E G} (hne : x₁ ≠ x₂) (ho₁ : vv x₁ = some o₁) (ho₂ : vv x₂ = some o₂)
    (hO₁ : o₁.IsO) (hO₂ : o₂.IsO) (hn₁ : V u ++ [o₁] <+: p ++ [m₁])
    (hn₂ : V u ++ [o₂] <+: p ++ [m₂]) (hm₁ : m₁.IsP) (hm₂ : m₂.IsP) : False := by
  rcases next_vis hn₁ with h₁ | ⟨-, rfl⟩
  · rcases next_vis hn₂ with h₂ | ⟨-, rfl⟩
    · exact hne (vv_inj ho₁ (prefix_same h₁ h₂ ▸ ho₂))
    · exact Move.not_isO_of_isP hm₂ hO₂
  · exact Move.not_isO_of_isP hm₁ hO₁

/-! ## The comparison of two interactions -/

/-- **Interactions after idle histories agree modulo traps.** -/
theorem agree_comp {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    {H₁ H₂ : List (Move E F)} {K₁ K₂ : List (Move F G)}
    (hσ : AgreeAfter tF σ H₁ H₂) (hτ : AgreeAfter tG τ K₁ K₂) (hst : Strict tF tG τ)
    (hH₁ : Path .idle H₁ .idle) (hH₂ : Path .idle H₂ .idle)
    (hK₁ : Path .idle K₁ .idle) (hK₂ : Path .idle K₂ .idle)
    {w₁ w₂ : List (Letter E F G)} {p : List (Move E G)} {m₁ m₂ : Move E G}
    (hs₁ : H₁ ++ L w₁ ∈ σ) (ht₁ : K₁ ++ R w₁ ∈ τ) (hs₂ : H₂ ++ L w₂ ∈ σ)
    (ht₂ : K₂ ++ R w₂ ∈ τ) (hv₁ : V w₁ = p ++ [m₁]) (hv₂ : V w₂ = p ++ [m₂])
    (hm₁ : m₁.IsP) (hm₂ : m₂.IsP) (hp : TrapFree tG p) :
    m₁ = m₂ ∨ PTrap tG m₁ ∨ PTrap tG m₂ := by
  rcases lcp w₁ w₂ with h | h | ⟨u, x₁, x₂, r₁, r₂, hne, rfl, rfl⟩
  · have h' := h.filterMap vv
    change V w₁ <+: V w₂ at h'
    rw [hv₁, hv₂] at h'
    exact .inl (eq_of_concat_prefix h')
  · have h' := h.filterMap vv
    change V w₂ <+: V w₁ at h'
    rw [hv₁, hv₂] at h'
    exact .inl (eq_of_concat_prefix h').symm
  have h1 : V u <+: p ++ [m₁] := by
    rw [← hv₁, V_append]
    exact List.prefix_append _ _
  rcases List.prefix_concat_iff.1 h1 with hu | hVu
  · have h2 : V u <+: p ++ [m₂] := by
      rw [← hv₂, V_append]
      exact List.prefix_append _ _
    rw [hu] at h2
    exact .inl (eq_of_concat_prefix h2)
  have hfree : TrapFree tG (V u) := fun y hy => hp y (hVu.subset hy)
  have hn₁ : ∀ o, vv x₁ = some o → V u ++ [o] <+: p ++ [m₁] := by
    intro o ho
    rw [← hv₁]
    exact ⟨V r₁, by simp [ho]⟩
  have hn₂ : ∀ o, vv x₂ = some o → V u ++ [o] <+: p ++ [m₂] := by
    intro o ho
    rw [← hv₂]
    exact ⟨V r₂, by simp [ho]⟩
  have hp₁ : u ++ [x₁] <+: u ++ x₁ :: r₁ := ⟨r₁, by simp⟩
  have hp₂ : u ++ [x₂] <+: u ++ x₂ :: r₂ := ⟨r₂, by simp⟩
  obtain ⟨X, hX⟩ := path_after hH₁ (mem_pre_L hs₁ (List.prefix_append u (x₁ :: r₁)))
  obtain ⟨Y, hY⟩ := path_after hK₁ (mem_pre_R ht₁ (List.prefix_append u (x₁ :: r₁)))
  have hl₁ : ∀ z, lv x₁ = some z → ∃ x', Step X z x' := fun z hz =>
    step_after hH₁ hX (by simpa [hz] using mem_pre_L hs₁ hp₁)
  have hl₂ : ∀ z, lv x₂ = some z → ∃ x', Step X z x' := fun z hz =>
    step_after hH₂ hX (by simpa [hz] using mem_pre_L hs₂ hp₂)
  have hr₁ : ∀ y, rv x₁ = some y → ∃ y', Step Y y y' := fun y hy =>
    step_after hK₁ hY (by simpa [hy] using mem_pre_R ht₁ hp₁)
  have hr₂ : ∀ y, rv x₂ = some y → ∃ y', Step Y y y' := fun y hy =>
    step_after hK₂ hY (by simpa [hy] using mem_pre_R ht₂ hp₂)
  have hc : Coh X Y := coh_path .idle u hX hY
  cases hc with
  | idle =>
    obtain ⟨o₁, ho₁, hO₁⟩ := turn_o_idle hl₁ hr₁
    obtain ⟨o₂, ho₂, hO₂⟩ := turn_o_idle hl₂ hr₂
    exact (o_case hne ho₁ ho₂ hO₁ hO₂ (hn₁ o₁ ho₁) (hn₂ o₂ ho₂) hm₁ hm₂).elim
  | wait q m e =>
    obtain ⟨o₁, ho₁, hO₁⟩ := turn_o_wait hl₁ hr₁
    obtain ⟨o₂, ho₂, hO₂⟩ := turn_o_wait hl₂ hr₂
    exact (o_case hne ho₁ ho₂ hO₁ hO₂ (hn₁ o₁ ho₁) (hn₂ o₂ ho₂) hm₁ hm₂).elim
  | run q =>
    show m₁ = m₂ ∨ PTrap tG m₁ ∨ PTrap tG m₂
    obtain ⟨y₁, hy₁, hP₁⟩ := turn_t hl₁ hr₁
    obtain ⟨y₂, hy₂, hP₂⟩ := turn_t hl₂ hr₂
    have hRfree : TrapFree tG (R u) := by
      intro y hy htr
      obtain ⟨x, hx, hxy⟩ := List.mem_filterMap.1 hy
      obtain ⟨y', hy', htr'⟩ := rv_ptrap hxy htr
      exact hfree y' (List.mem_filterMap.2 ⟨x, hx, hy'⟩) htr'
    have hm₁' : K₁ ++ R u ++ [y₁] ∈ τ := by simpa [hy₁] using mem_pre_R ht₁ hp₁
    have hm₂' : K₂ ++ R u ++ [y₂] ∈ τ := by simpa [hy₂] using mem_pre_R ht₂ hp₂
    rcases hτ (R u) y₁ y₂ hm₁' hm₂' hP₁ hP₂ hRfree with h | h | h
    · exact absurd (rv_inj hy₁ (h ▸ hy₂)) hne
    · obtain ⟨o, ho, hto⟩ := rv_ptrap hy₁ h
      rcases next_vis (hn₁ o ho) with h' | ⟨-, rfl⟩
      · exact absurd hto (hp o (h'.subset (by simp)))
      · exact .inr (.inl hto)
    · obtain ⟨o, ho, hto⟩ := rv_ptrap hy₂ h
      rcases next_vis (hn₂ o ho) with h' | ⟨-, rfl⟩
      · exact absurd hto (hp o (h'.subset (by simp)))
      · exact .inr (.inr hto)
  | sub q m =>
    show m₁ = m₂ ∨ PTrap tG m₁ ∨ PTrap tG m₂
    obtain ⟨z₁, hz₁, hP₁⟩ := turn_s hl₁ hr₁
    obtain ⟨z₂, hz₂, hP₂⟩ := turn_s hl₂ hr₂
    have hLfree : TrapFree tF (L u) := by
      intro z hz htr
      obtain ⟨x, hx, hxz⟩ := List.mem_filterMap.1 hz
      obtain ⟨m', n', rfl, htr'⟩ := lv_ptrap hxz htr
      obtain ⟨u₁, u₂, rfl⟩ := List.append_of_mem hx
      cases u₂ with
      | nil =>
        have hX' : Path .idle (L u₁ ++ [.inr (.ans m' n')]) (.run m) := by simpa [lv] using hX
        obtain ⟨_, -, hst'⟩ := Path.concat_iff.1 hX'
        cases hst'
      | cons x' u₂ =>
        have hpre : u₁ ++ [.inr (.inl (.ans m' n')), x'] <+:
            u₁ ++ .inr (.inl (.ans m' n')) :: x' :: u₂ ++ x₁ :: r₁ := ⟨u₂ ++ x₁ :: r₁, by simp⟩
        obtain ⟨q', v, rfl, htv⟩ :=
          after_trap hst htr' (mem_pre_L hs₁ hpre) (mem_pre_R ht₁ hpre)
        exact hfree (.inr (.ans q' v)) (by simp [vv]) htv
    have hm₁' : H₁ ++ L u ++ [z₁] ∈ σ := by simpa [hz₁] using mem_pre_L hs₁ hp₁
    have hm₂' : H₂ ++ L u ++ [z₂] ∈ σ := by simpa [hz₂] using mem_pre_L hs₂ hp₂
    rcases hσ (L u) z₁ z₂ hm₁' hm₂' hP₁ hP₂ hLfree with h | h | h
    · exact absurd (lv_inj hz₁ (h ▸ hz₂)) hne
    · obtain ⟨m', n', rfl, htr'⟩ := lv_ptrap hz₁ h
      exact .inr (.inl (hidden_trap hst htr' hs₁ ht₁ hv₁ hVu hp))
    · obtain ⟨m', n', rfl, htr'⟩ := lv_ptrap hz₂ h
      exact .inr (.inr (hidden_trap hst htr' hs₂ ht₂ hv₂ hVu hp))

end Silmaril.Proofs.Wasm.Det.Game

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F G : Sig.{u}}

/-! ## Splitting an interaction at a visible move -/

/-- Split an interaction at a visible move. -/
theorem split_vis : ∀ {w : List (Letter E F G)} {a b : List (Move E G)} {o : Move E G},
    V w = a ++ o :: b →
      ∃ W x r, w = W ++ x :: r ∧ V W = a ∧ vv x = some o ∧ V r = b
  | [], a, b, o, h => by simp at h
  | x :: w, a, b, o, h => by
    cases hx : vv x with
    | none =>
      rw [V_cons, hx, Option.toList_none, List.nil_append] at h
      obtain ⟨W, y, r, rfl, h₁, h₂, h₃⟩ := split_vis h
      exact ⟨x :: W, y, r, rfl, by simp [hx, h₁], h₂, h₃⟩
    | some o' =>
      rw [V_cons, hx, Option.toList_some, List.singleton_append] at h
      cases a with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact ⟨[], x, w, rfl, rfl, hx, h⟩
      | cons a₀ a =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨W, y, r, rfl, h₁, h₂, h₃⟩ := split_vis h
        exact ⟨x :: W, y, r, rfl, by simp [hx, h₁], h₂, h₃⟩

/-- After `τ`'s answer to an upper question, both plays are idle. -/
theorem idle_after {σ : Strategy E F} {τ : Strategy F G} {W : List (Letter E F G)} {q : G.Op}
    {v : G.Ar q} (hs : L (W ++ [ofV (.inr (.ans q v))]) ∈ σ)
    (ht : R (W ++ [ofV (.inr (.ans q v))]) ∈ τ) :
    Path .idle (L (W ++ [ofV (.inr (.ans q v))])) .idle ∧
      Path .idle (R (W ++ [ofV (.inr (.ans q v))])) .idle := by
  obtain ⟨X, hX⟩ : ∃ X, Path .idle (L (W ++ [ofV (.inr (.ans q v))])) X :=
    path_after (H := []) (.nil _) hs
  obtain ⟨Y, hY⟩ : ∃ Y, Path .idle (R (W ++ [ofV (.inr (.ans q v))])) Y :=
    path_after (H := []) (.nil _) ht
  have hc : Coh X Y := coh_path .idle _ hX hY
  have hY' : Path .idle (R W ++ [.inr (.ans q v)]) Y := by simpa [ofV, rv] using hY
  obtain ⟨_, -, hst⟩ := Path.concat_iff.1 hY'
  cases hst
  cases hc
  exact ⟨hX, hY⟩

/-- An interaction whose visible play starts with a play ending idle splits there, with both
plays idle. -/
theorem split_idle {σ : Strategy E F} {τ : Strategy F G} {w : List (Letter E F G)}
    {h c : List (Move E G)} (hs : L w ∈ σ) (ht : R w ∈ τ) (hv : V w = h ++ c)
    (hh : Path .idle h .idle) :
    ∃ W w', w = W ++ w' ∧ V w' = c ∧ Path .idle (L W) .idle ∧ Path .idle (R W) .idle := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, o, rfl⟩
  · exact ⟨[], w, rfl, by simpa using hv, .nil _, .nil _⟩
  have hh' : Path .idle (h₀ ++ [o]) .idle := by simpa using hh
  obtain ⟨y, -, hy⟩ := Path.concat_iff.1 hh'
  cases hy with
  | ret q v =>
    obtain ⟨W, x, r, hw, -, hx, hr⟩ := split_vis (a := h₀) (by simpa using hv)
    have hw' : w = W ++ ofV (.inr (.ans q v)) :: r := by rw [hw, vv_eq hx]
    have hpre : W ++ [ofV (.inr (.ans q v))] <+: w := ⟨r, by simp [hw']⟩
    exact ⟨_, r, by simp [hw'], hr, idle_after (σ.of_prefix hs (hpre.filterMap lv))
      (τ.of_prefix ht (hpre.filterMap rv))⟩

end Silmaril.Proofs.Wasm.Det.Game

namespace Silmaril.Proofs.Wasm.Det.Game

open Silmaril.Games Silmaril.Wasm.Det.Game

universe u

variable {E F G : Sig.{u}}

/-! ## The composite strategy -/

theorem agreeAfter_nil {tF : Traps F} {σ : Strategy E F} :
    AgreeAfter tF σ [] [] ↔ DetMod tF σ := by
  simp [AgreeAfter, DetMod]

/-- **Composition preserves determinism modulo traps** (the consumer `τ` is strict). -/
theorem detMod_comp {tF : Traps F} {tG : Traps G} {σ : Strategy E F} {τ : Strategy F G}
    (hσ : DetMod tF σ) (hτ : DetMod tG τ) (hst : Strict tF tG τ) : DetMod tG (σ.comp τ) := by
  rintro p m₁ m₂ ⟨s₁, hs₁, t₁, ht₁, hz₁⟩ ⟨s₂, hs₂, t₂, ht₂, hz₂⟩ hm₁ hm₂ hp
  obtain ⟨w₁, rfl, rfl, hv₁⟩ := zip_inter hz₁
  obtain ⟨w₂, rfl, rfl, hv₂⟩ := zip_inter hz₂
  exact agree_comp (H₁ := []) (H₂ := []) (K₁ := []) (K₂ := []) (agreeAfter_nil.2 hσ)
    (agreeAfter_nil.2 hτ) hst (.nil _) (.nil _) (.nil _) (.nil _) hs₁ ht₁ hs₂ ht₂ hv₁ hv₂ hm₁
    hm₂ hp

/-- **Composition preserves statelessness modulo traps** (the consumer `τ` is strict). -/
theorem statelessMod_comp {tF : Traps F} {tG : Traps G} {σ : Strategy E F}
    {τ : Strategy F G} (hσ : StatelessMod tF σ) (hτ : StatelessMod tG τ)
    (hst : Strict tF tG τ) : StatelessMod tG (σ.comp τ) := by
  intro h₁ h₂ _ _ hh₁ hh₂ c m₁ m₂ hc₁ hc₂ hm₁ hm₂ hc
  obtain ⟨s₁, hs₁, t₁, ht₁, hz₁⟩ := hc₁
  obtain ⟨s₂, hs₂, t₂, ht₂, hz₂⟩ := hc₂
  obtain ⟨w₁, rfl, rfl, hv₁⟩ := zip_inter hz₁
  obtain ⟨w₂, rfl, rfl, hv₂⟩ := zip_inter hz₂
  obtain ⟨W₁, w₁', rfl, hw₁, hL₁, hR₁⟩ :=
    split_idle hs₁ ht₁ (by rw [hv₁, List.append_assoc]) hh₁
  obtain ⟨W₂, w₂', rfl, hw₂, hL₂, hR₂⟩ :=
    split_idle hs₂ ht₂ (by rw [hv₂, List.append_assoc]) hh₂
  rw [L_append] at hs₁ hs₂
  rw [R_append] at ht₁ ht₂
  have hLW₁ : L W₁ ∈ σ := σ.of_prefix hs₁ (List.prefix_append _ _)
  have hLW₂ : L W₂ ∈ σ := σ.of_prefix hs₂ (List.prefix_append _ _)
  have hRW₁ : R W₁ ∈ τ := τ.of_prefix ht₁ (List.prefix_append _ _)
  have hRW₂ : R W₂ ∈ τ := τ.of_prefix ht₂ (List.prefix_append _ _)
  exact agree_comp (hσ _ _ hLW₁ hLW₂ hL₁ hL₂) (hτ _ _ hRW₁ hRW₂ hR₁ hR₂) hst hL₁ hL₂ hR₁ hR₂
    hs₁ ht₁ hs₂ ht₂ hw₁ hw₂ hm₁ hm₂ hc

/-- The letter after a lower trap answer, `τ` waiting. -/
theorem strict_next_letter {tE : Traps E} {tF : Traps F} {σ : Strategy E F} {τ : Strategy F G}
    (hσ : Strict tE tF σ) {W : List (Letter E F G)} {e : E.Op} {n : E.Ar e}
    {x : Letter E F G} {q : G.Op} {m : F.Op} (htr : tE e n)
    (hs : L (W ++ [.inl (.ans e n), x]) ∈ σ) (ht : R (W ++ [.inl (.ans e n), x]) ∈ τ)
    (hY : Path .idle (R W) (.wait q m)) : ∃ m n', x = .inr (.inl (.ans m n')) ∧ tF m n' := by
  rcases x with a | (b | ⟨b, n'⟩) | c
  · exact (hσ (L W) e n (.inl a) (by simpa [lv] using hs) htr).elim
  · exact (hσ (L W) e n (.inr (.ask b)) (by simpa [lv] using hs) htr).elim
  · exact ⟨b, n', rfl, hσ (L W) e n (.inr (.ans b n')) (by simpa [lv] using hs) htr⟩
  · exfalso
    obtain ⟨Y', hY'⟩ := τ.legal ht
    have hY'' : Path .idle (R W ++ [.inr c]) Y' := by simpa [rv] using hY'
    obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hY''
    rw [Path.det hy hY] at hst
    cases hst

/-- After a lower trap answer, `σ`'s strictness makes the next letter a hidden trap. -/
theorem strict_next {tE : Traps E} {tF : Traps F} {σ : Strategy E F} {τ : Strategy F G}
    (hσ : Strict tE tF σ) {W : List (Letter E F G)} {e : E.Op} {n : E.Ar e}
    {x : Letter E F G} (htr : tE e n) (hs : L (W ++ [.inl (.ans e n), x]) ∈ σ)
    (ht : R (W ++ [.inl (.ans e n), x]) ∈ τ) :
    ∃ m n', x = .inr (.inl (.ans m n')) ∧ tF m n' := by
  have hpre : W ++ [.inl (.ans e n)] <+: W ++ [.inl (.ans e n), x] := ⟨[x], by simp⟩
  obtain ⟨X, hX⟩ : ∃ X, Path .idle (L (W ++ [.inl (.ans e n)])) X :=
    path_after (H := []) (.nil _) (σ.of_prefix hs (hpre.filterMap lv))
  obtain ⟨Y, hY⟩ : ∃ Y, Path .idle (R (W ++ [.inl (.ans e n)])) Y :=
    path_after (H := []) (.nil _) (τ.of_prefix ht (hpre.filterMap rv))
  have hc : Coh X Y := coh_path .idle _ hX hY
  have hX' : Path .idle (L W ++ [.inl (.ans e n)]) X := by simpa [lv] using hX
  obtain ⟨_, -, hst⟩ := Path.concat_iff.1 hX'
  cases hst
  cases hc
  rename_i m q
  have hY' : Path .idle (R W) (.wait q m) := by simpa [rv] using hY
  exact strict_next_letter hσ htr hs ht hY'

/-- **Composition preserves strictness.** -/
theorem strict_comp {tE : Traps E} {tF : Traps F} {tG : Traps G} {σ : Strategy E F}
    {τ : Strategy F G} (hσ : Strict tE tF σ) (hτ : Strict tF tG τ) :
    Strict tE tG (σ.comp τ) := by
  rintro p e n b ⟨s, hs, t, ht, hz⟩ htr
  obtain ⟨w, hL, hR, hv⟩ := zip_inter hz
  obtain ⟨W, x, r, hw, -, hx, hr⟩ :=
    split_vis (a := p) (b := [b]) (o := .inl (.ans e n)) (by simpa using hv)
  have hw' : w = W ++ .inl (.ans e n) :: r := by rw [hw, vv_eq hx]; rfl
  have hsw : [] ++ L w ∈ σ := by rw [List.nil_append, hL]; exact hs
  have htw : [] ++ R w ∈ τ := by rw [List.nil_append, hR]; exact ht
  match r, hr, hw' with
  | [], hr, _ => exact absurd hr (by simp)
  | [x₁], hr, hw' =>
    have hp₁ : W ++ [.inl (.ans e n), x₁] <+: w := ⟨[], by simp [hw']⟩
    obtain ⟨m', n', rfl, -⟩ := strict_next hσ htr (by simpa using mem_pre_L hsw hp₁)
      (by simpa using mem_pre_R htw hp₁)
    exact absurd hr (by simp [vv])
  | x₁ :: x₂ :: r, hr, hw' =>
    show PTrap tG b
    have hp₁ : W ++ [.inl (.ans e n), x₁] <+: w := ⟨x₂ :: r, by simp [hw']⟩
    obtain ⟨m', n', rfl, htm⟩ := strict_next hσ htr (by simpa using mem_pre_L hsw hp₁)
      (by simpa using mem_pre_R htw hp₁)
    have hp₂ : (W ++ [.inl (.ans e n)]) ++ [.inr (.inl (.ans m' n')), x₂] <+: w :=
      ⟨r, by simp [hw']⟩
    obtain ⟨q', v, rfl, htv⟩ := after_trap hτ htm
      (mem_pre_L hsw hp₂) (mem_pre_R htw hp₂)
    have hb : b = .inr (.ans q' v) := by simpa [vv] using (List.cons.inj hr).1.symm
    rw [hb]
    exact htv

end Silmaril.Proofs.Wasm.Det.Game
