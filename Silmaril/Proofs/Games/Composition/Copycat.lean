module

public import Silmaril.Games.Strategy.Defs

/-!
# Copycat plays: legality and receptiveness

The plays of the copycat strategy are the prefixes of `Ev.double w` for an
alternating `w`. This module shows that they are legal and receptive; it is
used by `Silmaril.Games.Composition.Defs` to build `Strategy.id`.
-/

public section

namespace Silmaril.Proofs.Games.Composition

open Silmaril.Games

universe u

variable {E : Sig.{u}}

@[simp] theorem double_nil : Ev.double ([] : List (Ev E)) = [] := rfl

@[simp] theorem double_cons (x : Ev E) (w : List (Ev E)) :
    Ev.double (x :: w) = Ev.copy x ++ Ev.double w := by
  simp [Ev.double]

@[simp] theorem copy_ask (m : E.Op) : Ev.copy (.ask m) = [.inr (.ask m), .inl (.ask m)] := rfl

@[simp] theorem copy_ans (m : E.Op) (n : E.Ar m) :
    Ev.copy (.ans m n) = [.inl (.ans m n), .inr (.ans m n)] := rfl

theorem path_double {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∃ x, Path .idle (Ev.double w) x := by
  induction hw with
  | nil => exact ⟨_, .nil _⟩
  | ask m => exact ⟨_, .cons (.ask m) (.cons (.call m m) (.nil _))⟩
  | cons m n _ ih =>
    obtain ⟨x, hx⟩ := ih
    simp only [double_cons, copy_ask, copy_ans, List.cons_append, List.nil_append]
    exact ⟨x, .cons (.ask m) (.cons (.call m m) (.cons (.reply m m n) (.cons (.ret m n) hx)))⟩

theorem legal_of_prefix_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) : Legal c :=
  Legal.of_prefix (path_double hw) hc

private theorem receptive_idle {o : Move E E} {y : Pos E E} (h : Step .idle o y) :
    ∃ w', Ev.Alternating w' ∧ [] ++ [o] <+: Ev.double w' := by
  cases h with
  | ask m => exact ⟨[.ask m], .ask m, by simp⟩

/-- A prefix of `a :: b :: rest` is empty, `[a]`, or `a :: b` followed by a prefix of `rest`. -/
private theorem prefix_pair_cases {α : Type u} {a b : α} {c rest : List α}
    (hc : c <+: a :: b :: rest) :
    c = [] ∨ c = [a] ∨ ∃ c', c = a :: b :: c' ∧ c' <+: rest := by
  rcases List.prefix_cons_iff.1 hc with h0 | ⟨c₁, hc₁, hp₁⟩
  · exact .inl h0
  rcases List.prefix_cons_iff.1 hp₁ with h1 | ⟨c₂, hc₂, hp₂⟩
  · exact .inr (.inl (by rw [hc₁, h1]))
  · exact .inr (.inr ⟨c₂, by rw [hc₁, hc₂], hp₂⟩)

/-- Receptiveness of the empty play. -/
private theorem receptive_empty {c : List (Move E E)} {x y : Pos E E} {o : Move E E}
    (hc : c = []) (hx : Path .idle c x) (hxy : Step x o y) :
    ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' := by
  subst hc
  cases hx
  exact receptive_idle hxy

/-- After an upper question, Proponent must move. -/
private theorem not_receptive_asked {m : E.Op} {c : List (Move E E)} {x y : Pos E E}
    {o : Move E E} (hc : c = [.inr (.ask m)]) (hx : Path .idle c x) (hxy : Step x o y)
    (ho : o.IsO) : False := by
  subst hc
  cases hx with
  | cons h₁ hp => cases h₁; cases hp; cases hxy <;> exact ho.elim

/-- After a question has been forwarded, Opponent can only answer it. -/
private theorem receptive_called {m : E.Op} {c : List (Move E E)} {x y : Pos E E}
    {o : Move E E} (hc : c = [.inr (.ask m), .inl (.ask m)]) (hx : Path .idle c x)
    (hxy : Step x o y) : ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' := by
  subst hc
  cases hx with
  | cons h₁ hp =>
    cases h₁
    cases hp with
    | cons h₂ hp =>
      cases h₂; cases hp
      cases hxy with
      | reply _ _ n => exact ⟨[.ask m, .ans m n], .cons m n .nil, by simp⟩

/-- After the lower answer has arrived, Proponent must move. -/
private theorem not_receptive_replied {m : E.Op} {n : E.Ar m} {c : List (Move E E)}
    {x y : Pos E E} {o : Move E E}
    (hc : c = [.inr (.ask m), .inl (.ask m), .inl (.ans m n)]) (hx : Path .idle c x)
    (hxy : Step x o y) (ho : o.IsO) : False := by
  subst hc
  cases hx with
  | cons h₁ hp =>
    cases h₁
    cases hp with
    | cons h₂ hp =>
      cases h₂
      cases hp with
      | cons h₃ hp => cases h₃; cases hp; cases hxy <;> exact ho.elim

/-- A completed copied exchange returns the automaton to idle. -/
private theorem path_of_copy_four {m : E.Op} {n : E.Ar m} {c : List (Move E E)} {x : Pos E E}
    (hx : Path .idle
      (.inr (.ask m) :: .inl (.ask m) :: .inl (.ans m n) :: .inr (.ans m n) :: c) x) :
    Path .idle c x := by
  cases hx with
  | cons h₁ hp =>
    cases h₁
    cases hp with
    | cons h₂ hp =>
      cases h₂
      cases hp with
      | cons h₃ hp =>
        cases h₃
        cases hp with
        | cons h₄ hp => cases h₄; exact hp

theorem receptive_double {w : List (Ev E)} (hw : Ev.Alternating w) :
    ∀ {c : List (Move E E)}, c <+: Ev.double w → ∀ {x y : Pos E E} {o : Move E E},
      Path .idle c x → Step x o y → o.IsO →
      ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' := by
  induction hw with
  | nil =>
    intro c hc x y o hx hxy _
    have hc0 : c = [] := List.prefix_nil.1 (by simpa only [double_nil] using hc)
    exact receptive_empty hc0 hx hxy
  | ask m =>
    show ∀ {c : List (Move E E)}, c <+: Ev.double [.ask m] →
      ∀ {x y : Pos E E} {o : Move E E}, Path .idle c x → Step x o y → o.IsO →
        ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w'
    intro c hc x y o hx hxy ho
    have hc' : c <+: [.inr (.ask m), .inl (.ask m)] := by
      simpa only [double_cons, copy_ask, double_nil, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c', hcc, hc''⟩
    · exact receptive_empty h0 hx hxy
    · exact (not_receptive_asked h1 hx hxy ho).elim
    · have hc0 : c' = [] := List.prefix_nil.1 hc''
      exact receptive_called (by rw [hcc, hc0]) hx hxy
  | @cons m n w _ ih =>
    show ∀ {c : List (Move E E)}, c <+: Ev.double (.ask m :: .ans m n :: w) →
      ∀ {x y : Pos E E} {o : Move E E}, Path .idle c x → Step x o y → o.IsO →
        ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w'
    intro c hc x y o hx hxy ho
    have hc' : c <+: .inr (.ask m) :: .inl (.ask m) ::
        .inl (.ans m n) :: .inr (.ans m n) :: Ev.double w := by
      simpa only [double_cons, copy_ask, copy_ans, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c₁, hcc₁, hc₁⟩
    · exact receptive_empty h0 hx hxy
    · exact (not_receptive_asked h1 hx hxy ho).elim
    rcases prefix_pair_cases hc₁ with h0 | h1 | ⟨c₂, hcc₂, hc₂⟩
    · exact receptive_called (by rw [hcc₁, h0]) hx hxy
    · exact (not_receptive_replied (by rw [hcc₁, h1]) hx hxy ho).elim
    have hcc : c = .inr (.ask m) :: .inl (.ask m) :: .inl (.ans m n) :: .inr (.ans m n) :: c₂ := by
      rw [hcc₁, hcc₂]
    have hp : Path .idle c₂ x := path_of_copy_four (hcc ▸ hx)
    obtain ⟨w', hw', hp'⟩ : ∃ w', Ev.Alternating w' ∧ c₂ ++ [o] <+: Ev.double w' :=
      ih hc₂ hp hxy ho
    have hpre : c ++ [o] <+: Ev.double (.ask m :: .ans m n :: w') := by
      rw [hcc]
      simpa using hp'
    exact ⟨_, .cons m n hw', hpre⟩

end Silmaril.Proofs.Games.Composition
