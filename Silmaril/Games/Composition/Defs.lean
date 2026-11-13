module

public import Silmaril.Games.Strategy.Defs
public import Silmaril.Games.Zip.Defs

/-!
# Composition and copycat

* `σ.comp τ : Strategy E G` for `σ : Strategy E F` and `τ : Strategy F G`
  (diagrammatic order, as Mathlib's `≫`): `τ` implements `G` by calling `F`,
  whose calls `σ` serves by calling `E`. Its plays are the visible traces of
  the interactions (`Zip`) of a play of `σ` with a play of `τ`; the `F`-moves
  are hidden.
* `Strategy.id E : Strategy E E` is copycat: it forwards each question from
  the right to the left and each answer from the left to the right. Its plays
  are the prefixes of `Ev.double w` for alternating `w`.

Legality, prefix closure and receptiveness of the composite and of copycat are
proved here, since the proof fields of `comp` and `Strategy.id` need them: the
interaction is tracked through the three automaton positions (`ZipCompat`
lists the four reachable combinations). The laws (unit, associativity,
monotonicity) are in `Silmaril.Games.Composition.Thms`.
-/

@[expose] public section

namespace Silmaril.Games

universe u

namespace Strategy

variable {E F G : Sig.{u}}

/-! ## Legality and receptiveness of composites -/

/-- The reachable combinations of positions during an interaction. -/
inductive ZipCompat : Pos E F → Pos F G → Pos E G → Prop
  | idle : ZipCompat .idle .idle .idle
  | run (g : G.Op) : ZipCompat .idle (.run g) (.run g)
  | call (g : G.Op) (f : F.Op) : ZipCompat (.run f) (.wait g f) (.run g)
  | wait (g : G.Op) (f : F.Op) (e : E.Op) : ZipCompat (.wait f e) (.wait g f) (.wait g e)

/-- The positions reached along an interaction are compatible. -/
theorem zip_path {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ {a b c a' b'}, ZipCompat a b c → Path a s a' → Path b t b' →
      ∃ c', Path c p c' ∧ ZipCompat a' b' c' := by
  induction h with
  | nil =>
    intro a b c a' b' hc hs ht
    cases hs; cases ht
    exact ⟨c, .nil _, hc⟩
  | @left s t p x _ ih =>
    show ∀ {a b c a' b'}, ZipCompat a b c → Path a (.inl x :: s) a' → Path b t b' →
      ∃ c', Path c (.inl x :: p) c' ∧ ZipCompat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hst hs =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (ZipCompat.wait _ _ _) hs ht
        exact ⟨c', .cons (.call _ _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih (ZipCompat.call _ _) hs ht
        exact ⟨c', .cons (.reply _ _ _) hp, hc'⟩
  | @right s t p y _ ih =>
    show ∀ {a b c a' b'}, ZipCompat a b c → Path a s a' → Path b (.inr y :: t) b' →
      ∃ c', Path c (.inr y :: p) c' ∧ ZipCompat a' b' c'
    intro a b c a' b' hc hs ht
    cases ht with
    | cons hst ht =>
      cases hst <;> cases hc
      · obtain ⟨c', hp, hc'⟩ := ih (ZipCompat.run _) hs ht
        exact ⟨c', .cons (.ask _) hp, hc'⟩
      · obtain ⟨c', hp, hc'⟩ := ih ZipCompat.idle hs ht
        exact ⟨c', .cons (.ret _ _) hp, hc'⟩
  | @sync s t p z _ ih =>
    show ∀ {a b c a' b'}, ZipCompat a b c → Path a (.inr z :: s) a' → Path b (.inl z :: t) b' →
      ∃ c', Path c p c' ∧ ZipCompat a' b' c'
    intro a b c a' b' hc hs ht
    cases hs with
    | cons hs₁ hs =>
      cases ht with
      | cons ht₁ ht =>
        cases hs₁ <;> cases ht₁ <;> cases hc
        · exact ih (ZipCompat.call _ _) hs ht
        · exact ih (ZipCompat.run _) hs ht

/-- The interaction of legal plays is legal. -/
theorem legal_of_zip {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (hs : Legal s) (ht : Legal t) (h : Zip s t p) : Legal p := by
  obtain ⟨_, hs⟩ := hs
  obtain ⟨_, ht⟩ := ht
  obtain ⟨c, hp, -⟩ := zip_path h ZipCompat.idle hs ht
  exact ⟨c, hp⟩

/-- An Opponent move after an interaction can be absorbed by one of the two
strategies. -/
theorem receptive_of_zip (σ : Strategy E F) (τ : Strategy F G) {s : List (Move E F)}
    {t : List (Move F G)} {p : List (Move E G)} (hs : s ∈ σ) (ht : t ∈ τ) (h : Zip s t p)
    {x y : Pos E G} {o : Move E G} (hx : Path .idle p x) (hxy : Step x o y) (ho : o.IsO) :
    ∃ s' ∈ σ, ∃ t' ∈ τ, Zip s' t' (p ++ [o]) := by
  obtain ⟨a, ha⟩ := σ.legal hs
  obtain ⟨b, hb⟩ := τ.legal ht
  obtain ⟨c, hc, hcomp⟩ := zip_path h ZipCompat.idle ha hb
  cases hx.det hc
  cases hxy with
  | ask g =>
    cases hcomp
    exact ⟨s, hs, _, τ.receptive ht hb (.ask g) trivial, h.append_right _⟩
  | reply g e n =>
    cases hcomp
    exact ⟨_, σ.receptive hs ha (.reply _ e n) trivial, t, ht, h.append_left _⟩
  | call => exact ho.elim
  | ret => exact ho.elim

end Strategy

/-! ## Copycat plays: legality and receptiveness -/

namespace Ev

variable {E : Sig.{u}}

/-- Copycat plays are paths from the idle position. -/
theorem path_double {w : List (Ev E)} (hw : Alternating w) :
    ∃ x, Path .idle (double w) x := by
  induction hw with
  | nil => exact ⟨_, .nil _⟩
  | ask m => exact ⟨_, .cons (.ask m) (.cons (.call m m) (.nil _))⟩
  | cons m n _ ih =>
    obtain ⟨x, hx⟩ := ih
    simp only [double_cons, copy_ask, copy_ans, List.cons_append, List.nil_append]
    exact ⟨x, .cons (.ask m) (.cons (.call m m) (.cons (.reply m m n) (.cons (.ret m n) hx)))⟩

private theorem receptive_idle {o : Move E E} {y : Pos E E} (h : Step .idle o y) :
    ∃ w', Alternating w' ∧ [] ++ [o] <+: double w' := by
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
    ∃ w', Alternating w' ∧ c ++ [o] <+: double w' := by
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
    (hxy : Step x o y) : ∃ w', Alternating w' ∧ c ++ [o] <+: double w' := by
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

/-- Copycat plays are receptive (by induction on the forwarded exchanges). -/
private theorem receptive_double_aux {w : List (Ev E)} (hw : Alternating w) :
    ∀ {c : List (Move E E)}, c <+: double w → ∀ {x y : Pos E E} {o : Move E E},
      Path .idle c x → Step x o y → o.IsO →
      ∃ w', Alternating w' ∧ c ++ [o] <+: double w' := by
  induction hw with
  | nil =>
    intro c hc x y o hx hxy _
    have hc0 : c = [] := List.prefix_nil.1 (by simpa only [double_nil] using hc)
    exact receptive_empty hc0 hx hxy
  | ask m =>
    show ∀ {c : List (Move E E)}, c <+: double [.ask m] →
      ∀ {x y : Pos E E} {o : Move E E}, Path .idle c x → Step x o y → o.IsO →
        ∃ w', Alternating w' ∧ c ++ [o] <+: double w'
    intro c hc x y o hx hxy ho
    have hc' : c <+: [.inr (.ask m), .inl (.ask m)] := by
      simpa only [double_cons, copy_ask, double_nil, List.cons_append, List.nil_append] using hc
    rcases prefix_pair_cases hc' with h0 | h1 | ⟨c', hcc, hc''⟩
    · exact receptive_empty h0 hx hxy
    · exact (not_receptive_asked h1 hx hxy ho).elim
    · have hc0 : c' = [] := List.prefix_nil.1 hc''
      exact receptive_called (by rw [hcc, hc0]) hx hxy
  | @cons m n w _ ih =>
    show ∀ {c : List (Move E E)}, c <+: double (.ask m :: .ans m n :: w) →
      ∀ {x y : Pos E E} {o : Move E E}, Path .idle c x → Step x o y → o.IsO →
        ∃ w', Alternating w' ∧ c ++ [o] <+: double w'
    intro c hc x y o hx hxy ho
    have hc' : c <+: .inr (.ask m) :: .inl (.ask m) ::
        .inl (.ans m n) :: .inr (.ans m n) :: double w := by
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
    obtain ⟨w', hw', hp'⟩ : ∃ w', Alternating w' ∧ c₂ ++ [o] <+: double w' :=
      ih hc₂ hp hxy ho
    have hpre : c ++ [o] <+: double (.ask m :: .ans m n :: w') := by
      rw [hcc]
      simpa using hp'
    exact ⟨_, .cons m n hw', hpre⟩

end Ev

namespace Strategy

variable {E F G : Sig.{u}}

/-- Prefixes of copycat plays are legal. -/
theorem _root_.Silmaril.Games.Ev.legal_of_prefix_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) : Legal c :=
  Legal.of_prefix (Ev.path_double hw) hc

/-- Copycat plays are receptive. -/
theorem _root_.Silmaril.Games.Ev.receptive_double {w : List (Ev E)} (hw : Ev.Alternating w)
    {c : List (Move E E)} (hc : c <+: Ev.double w) {x y : Pos E E} {o : Move E E}
    (hx : Path .idle c x) (hxy : Step x o y) (ho : o.IsO) :
    ∃ w', Ev.Alternating w' ∧ c ++ [o] <+: Ev.double w' :=
  Ev.receptive_double_aux hw hc hx hxy ho

/-- Composition `σ.comp τ` (first `σ`, then `τ`): `τ : F ↠ G` runs on top of
`σ : E ↠ F`, the interactions at `F` are hidden. -/
def comp (σ : Strategy E F) (τ : Strategy F G) : Strategy E G where
  plays := {p | ∃ s ∈ σ, ∃ t ∈ τ, Zip s t p}
  nil_mem := ⟨[], σ.nil_mem, [], τ.nil_mem, .nil⟩
  legal := fun ⟨_, hs, _, ht, h⟩ =>
    legal_of_zip (σ.legal hs) (τ.legal ht) h
  of_prefix := fun ⟨_, hs, _, ht, h⟩ hq => by
    obtain ⟨s', t', hs', ht', h'⟩ := h.of_prefix hq
    exact ⟨s', σ.of_prefix hs hs', t', τ.of_prefix ht ht', h'⟩
  receptive := fun ⟨_, hs, _, ht, h⟩ hx hxy ho =>
    receptive_of_zip σ τ hs ht h hx hxy ho

/-- The plays of a composite are the visible parts of interactions. -/
theorem mem_comp {σ : Strategy E F} {τ : Strategy F G} {p : List (Move E G)} :
    p ∈ σ.comp τ ↔ ∃ s ∈ σ, ∃ t ∈ τ, Zip s t p := Iff.rfl

/-- The copycat strategy: the identity on `E`. -/
protected def id (E : Sig.{u}) : Strategy E E where
  plays := {c | ∃ w, Ev.Alternating w ∧ c <+: Ev.double w}
  nil_mem := ⟨[], .nil, List.nil_prefix⟩
  legal := fun ⟨_, hw, hc⟩ => Ev.legal_of_prefix_double hw hc
  of_prefix := fun ⟨w, hw, hc⟩ h => ⟨w, hw, h.trans hc⟩
  receptive := fun ⟨_, hw, hc⟩ hx hxy ho =>
    Ev.receptive_double hw hc hx hxy ho

/-- The plays of copycat. -/
theorem mem_id {c : List (Move E E)} :
    c ∈ Strategy.id E ↔ ∃ w, Ev.Alternating w ∧ c <+: Ev.double w := Iff.rfl

end Strategy

end Silmaril.Games
