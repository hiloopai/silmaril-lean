module

public import Silmaril.Games.Institution.Defs

/-!
# The upper half of the reduct: proofs

Proofs for `Strategy.restrict_sound` in `Silmaril.Games.Institution.Thms`. Every play of
`σ.restrict ρ` is the `UpRel ρ`-image of a play of `σ`, possibly followed by one question
that has not been forwarded yet.

The proof runs the transition system `σ.toLTS.comp (Handler.ofHom ρ).toReduction.toLTS`, which
denotes `σ.restrict ρ` (`LTS.Denotes.comp`), and keeps the invariant `Inv`. The invariant
relates the play `s` of `σ` reached so far, the state of the forwarding handler and the
visible play `p`.
-/

public section

namespace Silmaril.Proofs.Games.Institution

open Silmaril.Games

universe u

variable {X G F : Sig.{u}} (σ : Strategy X F) (ρ : Sig.Hom G F)

/-- The reduction semantics of the forwarding handler of `ρ`. -/
abbrev Fwd : Reduction F G := (Handler.ofHom ρ).toReduction

/-- The invariant of the restriction run. -/
@[expose] def Inv : List (Move X F) × (Fwd ρ).State → List (Move X G) → Prop
  | (s, .idle), p => s ∈ σ ∧ Path .idle s .idle ∧ List.Forall₂ (UpRel ρ) s p
  | (s, .run q c), p =>
      (c = Handler.ofHom ρ q ∧ s ∈ σ ∧ Path .idle s .idle ∧
        ∃ p', p = p' ++ [.inr (.ask q)] ∧ List.Forall₂ (UpRel ρ) s p') ∨
      (∃ n s', c = .pure (ρ.ar q n) ∧ s = s' ++ [.inr (.ans (ρ.op q) n)] ∧ s ∈ σ ∧
        List.Forall₂ (UpRel ρ) s' p)
  | (s, .wait q m k), p =>
      m = ρ.op q ∧ HEq k (fun n : F.Ar (ρ.op q) => (Prog.pure (ρ.ar q n) : Prog F (G.Ar q))) ∧
        s ∈ σ ∧ List.Forall₂ (UpRel ρ) s p

omit σ ρ in
/-- After an upper answer, the position is idle. -/
theorem idle_of_ans {s : List (Move X F)} {q : F.Op} {n : F.Ar q} {x : Pos X F}
    (h : Path .idle (s ++ [.inr (.ans q n)]) x) : x = .idle := by
  obtain ⟨_, -, hs⟩ := Path.concat_iff.1 h
  cases hs
  rfl

omit σ ρ in
/-- From the idle position no lower move is legal. -/
theorem no_low {s : List (Move X F)} {e : Ev X} (hs : Path .idle s .idle)
    (hl : Legal (s ++ [.inl e])) : False := by
  obtain ⟨_, h⟩ := hl
  obtain ⟨x, hx, hxe⟩ := Path.concat_iff.1 h
  cases Path.det hx hs
  cases hxe

omit σ in
/-- Extending related plays by related moves. -/
theorem forall₂_concat {s : List (Move X F)} {p : List (Move X G)} {a : Move X F}
    {b : Move X G} (h : List.Forall₂ (UpRel ρ) s p) (hab : UpRel ρ a b) :
    List.Forall₂ (UpRel ρ) (s ++ [a]) (p ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h₁ _ ih => exact .cons h₁ ih

/-- A lower move of `σ` keeps the invariant: it can only happen while a question is being
served, so the handler is waiting. -/
theorem inv_left {s : List (Move X F)} {z : (Fwd ρ).State} {e : Ev X} {p : List (Move X G)}
    (hm : s ++ [.inl e] ∈ σ) (hi : Inv σ ρ (s, z) p) :
    Inv σ ρ (s ++ [.inl e], z) (p ++ [.inl e]) := by
  rcases z with _ | ⟨q, c⟩ | ⟨q, m, k⟩
  · exact (no_low hi.2.1 (σ.legal hm)).elim
  · rcases hi with ⟨_, _, hpath, _⟩ | ⟨_, s₀, _, rfl, _, _⟩
    · exact (no_low hpath (σ.legal hm)).elim
    · obtain ⟨_, h⟩ := σ.legal hm
      obtain ⟨x, hx, hxe⟩ := Path.concat_iff.1 h
      cases idle_of_ans hx
      cases hxe
  · obtain ⟨hm', hk, _, hr⟩ := hi
    exact ⟨hm', hk, hm, forall₂_concat ρ hr (.low e)⟩

/-- A visible upper move of the handler keeps the invariant. -/
theorem inv_right {s : List (Move X F)} {z z' : (Fwd ρ).State} {g : Ev G}
    {p : List (Move X G)} (h : (Fwd ρ).Step z (some (.inr g)) z') (hi : Inv σ ρ (s, z) p) :
    Inv σ ρ (s, z') (p ++ [.inr g]) := by
  cases h with
  | ask q =>
    obtain ⟨hs, hpath, hr⟩ := hi
    exact .inl ⟨rfl, hs, hpath, p, rfl, hr⟩
  | @ret q c r hd =>
    rcases hi with ⟨hc, -⟩ | ⟨n, s₀, hc, rfl, hs, hr⟩
    · rw [hc] at hd
      cases hd
    · rw [hc] at hd
      cases hd
      obtain ⟨_, hpath⟩ := σ.legal hs
      refine ⟨hs, ?_, forall₂_concat ρ hr (.ans q n)⟩
      cases idle_of_ans hpath
      exact hpath

/-- A hidden synchronisation between `σ` and the handler keeps the invariant. -/
theorem inv_sync {s : List (Move X F)} {z z' : (Fwd ρ).State} {f : Ev F}
    {p : List (Move X G)} (hm : s ++ [.inr f] ∈ σ) (h : (Fwd ρ).Step z (some (.inl f)) z')
    (hi : Inv σ ρ (s, z) p) : Inv σ ρ (s ++ [.inr f], z') p := by
  cases h with
  | @call q c m k hc =>
    rcases hi with ⟨hc', -, -, p', rfl, hr⟩ | ⟨n, s₀, hc', -⟩
    · rw [hc'] at hc
      cases hc
      exact ⟨rfl, HEq.rfl, hm, forall₂_concat ρ hr (.ask q)⟩
    · rw [hc'] at hc
      cases hc
  | resume q m k n =>
    obtain ⟨rfl, hk, -, hr⟩ := hi
    cases hk
    exact .inr ⟨n, s, rfl, rfl, hm, hr⟩

/-- One step of the restriction run keeps the invariant. -/
theorem inv_step {x y : (σ.toLTS.comp (Fwd ρ).toLTS).State} {l : Option (Move X G)}
    {p : List (Move X G)} (hst : LTS.CompStep σ.toLTS (Fwd ρ).toLTS x l y)
    (hi : Inv σ ρ x p) : Inv σ ρ y (p ++ l.toList) := by
  cases hst with
  | tau₁ h => cases h
  | tau₂ h => cases h with | tau hc => exact (hc : False).elim
  | left e h => cases h with | mk _ hm => exact inv_left σ ρ hm hi
  | right g h => exact inv_right σ ρ h hi
  | sync f h₁ h₂ =>
    cases h₁ with
    | mk _ hm =>
      rw [Option.toList_none, List.append_nil]
      exact inv_sync σ ρ hm h₂ hi

/-- Runs of the restriction keep the invariant. -/
theorem inv_run {x y : (σ.toLTS.comp (Fwd ρ).toLTS).State} {t : List (Move X G)}
    (h : (σ.toLTS.comp (Fwd ρ).toLTS).Run x t y) :
    ∀ p, Inv σ ρ x p → Inv σ ρ y (p ++ t) := by
  induction h with
  | nil => intro p hp; simpa using hp
  | tau hst _ ih =>
    intro p hp
    exact ih p (by simpa using inv_step σ ρ hst hp)
  | @vis _ _ _ o t hst _ ih =>
    intro p hp
    simpa using ih _ (inv_step σ ρ hst hp)

/-- **Soundness of restriction**: every play of `σ.restrict ρ` is the image of a play of `σ`,
possibly followed by one question that has not been forwarded yet. -/
theorem restrict_sound {p : List (Move X G)} (hp : p ∈ σ.restrict ρ) :
    ∃ s ∈ σ, List.Forall₂ (UpRel ρ) s p ∨
      ∃ p' q, p = p' ++ [.inr (.ask q)] ∧ List.Forall₂ (UpRel ρ) s p' := by
  have hd := LTS.Denotes.comp σ.denotes_toLTS (Handler.ofHom ρ).denotes_toLTS
  obtain ⟨y, hy⟩ := (hd p).2 hp
  have hi : Inv σ ρ y ([] ++ p) :=
    inv_run σ ρ hy [] ⟨σ.nil_mem, .nil _, .nil⟩
  rw [List.nil_append] at hi
  match y, hi with
  | (s, .idle), ⟨hs, _, hr⟩ => exact ⟨s, hs, .inl hr⟩
  | (s, .run _ _), .inl ⟨_, hs, _, p', hp', hr⟩ => exact ⟨s, hs, .inr ⟨p', _, hp', hr⟩⟩
  | (_, .run _ _), .inr ⟨_, s₀, _, rfl, hs, hr⟩ =>
    exact ⟨s₀, σ.of_prefix hs (List.prefix_append _ _), .inl hr⟩
  | (s, .wait _ _ _), ⟨_, _, hs, hr⟩ => exact ⟨s, hs, .inl hr⟩

end Silmaril.Proofs.Games.Institution
