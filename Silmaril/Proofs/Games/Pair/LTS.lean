module

public import Silmaril.Games.Pair.Defs
public import Silmaril.Games.LTS.Thms

/-!
# The pairing of transition systems denotes the pairing of strategies

Proofs for `Silmaril.Games.Pair.Thms` (`LTS.Denotes.pair`).
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games Silmaril.Games.Split

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- Positions and the side of the current round agree. -/
inductive SideOK : Pos E (F₁ ⊕ₛ F₂) → Bool → Prop
  | idle (b : Bool) : SideOK .idle b
  | runL (q : F₁.Op) : SideOK (.run (.inl q)) false
  | waitL (q : F₁.Op) (m : E.Op) : SideOK (.wait (.inl q) m) false
  | runR (q : F₂.Op) : SideOK (.run (.inr q)) true
  | waitR (q : F₂.Op) (m : E.Op) : SideOK (.wait (.inr q) m) true

theorem halves_nil (b : Bool) :
    halves b ([] : List (Move E (F₁ ⊕ₛ F₂))) = ([], []) := by cases b <;> rfl

theorem halves_askL (b : Bool) (q : F₁.Op) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves b (.inr (.ask (.inl q)) :: s) = (.inr (.ask q) :: (halves false s).1, (halves false s).2) := by
  cases b <;> rfl

theorem halves_askR (b : Bool) (q : F₂.Op) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves b (.inr (.ask (.inr q)) :: s) = ((halves true s).1, .inr (.ask q) :: (halves true s).2) := by
  cases b <;> rfl

theorem halves_retL (b : Bool) (q : F₁.Op) (r : F₁.Ar q) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves b (.inr (.ans (.inl q) r) :: s) = (.inr (.ans q r) :: (halves b s).1, (halves b s).2) := by
  cases b <;> rfl

theorem halves_retR (b : Bool) (q : F₂.Op) (r : F₂.Ar q) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves b (.inr (.ans (.inr q) r) :: s) = ((halves b s).1, .inr (.ans q r) :: (halves b s).2) := by
  cases b <;> rfl

theorem halves_inl_false (e : Ev E) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves false (.inl e :: s) = (.inl e :: (halves false s).1, (halves false s).2) := rfl

theorem halves_inl_true (e : Ev E) (s : List (Move E (F₁ ⊕ₛ F₂))) :
    halves true (.inl e :: s) = ((halves true s).1, .inl e :: (halves true s).2) := rfl

theorem pair_taus₁ {L₁ : LTS E F₁} {L₂ : LTS E F₂} (p : Pos E (F₁ ⊕ₛ F₂)) {x x' : L₁.State}
    (y : L₂.State) (h : L₁.Run x [] x') : (L₁.pair L₂).Run (p, x, y) [] (p, x', y) := by
  generalize hl : ([] : List (Move E F₁)) = l at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LTS.PairStep.tau₁ hs) (ih hl)
  | vis => cases hl

theorem pair_taus₂ {L₁ : LTS E F₁} {L₂ : LTS E F₂} (p : Pos E (F₁ ⊕ₛ F₂)) (x : L₁.State)
    {y y' : L₂.State} (h : L₂.Run y [] y') : (L₁.pair L₂).Run (p, x, y) [] (p, x, y') := by
  generalize hl : ([] : List (Move E F₂)) = l at h
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (LTS.PairStep.tau₂ hs) (ih hl)
  | vis => cases hl

theorem pair_run {L₁ : LTS E F₁} {L₂ : LTS E F₂} {z z' : (L₁.pair L₂).State}
    {s : List (Move E (F₁ ⊕ₛ F₂))} (h : (L₁.pair L₂).Run z s z') :
    ∀ {b}, SideOK z.1 b → Path z.1 s z'.1 ∧ L₁.Run z.2.1 (halves b s).1 z'.2.1 ∧
      L₂.Run z.2.2 (halves b s).2 z'.2.2 := by
  induction h with
  | nil =>
    intro b _
    rw [halves_nil]
    exact ⟨.nil _, .nil _, .nil _⟩
  | @tau z₁ z₂ z₃ s hs _ ih =>
    show ∀ {b}, SideOK z₁.1 b → Path z₁.1 s z₃.1 ∧ L₁.Run z₁.2.1 (halves b s).1 z₃.2.1 ∧
      L₂.Run z₁.2.2 (halves b s).2 z₃.2.2
    intro b hb
    cases hs with
    | tau₁ hs =>
      obtain ⟨hp, h₁, h₂⟩ := ih hb
      exact ⟨hp, .tau hs h₁, h₂⟩
    | tau₂ hs =>
      obtain ⟨hp, h₁, h₂⟩ := ih hb
      exact ⟨hp, h₁, .tau hs h₂⟩
  | @vis z₁ z₂ z₃ o s hs _ ih =>
    show ∀ {b}, SideOK z₁.1 b → Path z₁.1 (o :: s) z₃.1 ∧
      L₁.Run z₁.2.1 (halves b (o :: s)).1 z₃.2.1 ∧ L₂.Run z₁.2.2 (halves b (o :: s)).2 z₃.2.2
    intro b hb
    cases hs with
    | askL q hx =>
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.runL q)
      rw [halves_askL]
      exact ⟨.cons (Step.ask (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q)) hp, .vis hx h₁, h₂⟩
    | askR q hx =>
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.runR q)
      rw [halves_askR]
      exact ⟨.cons (Step.ask (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q)) hp, h₁, .vis hx h₂⟩
    | callL q m hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.waitL q m)
      rw [halves_inl_false]
      exact ⟨.cons (.call _ _) hp, .vis hx h₁, h₂⟩
    | callR q m hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.waitR q m)
      rw [halves_inl_true]
      exact ⟨.cons (.call _ _) hp, h₁, .vis hx h₂⟩
    | replyL q m n hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.runL q)
      rw [halves_inl_false]
      exact ⟨.cons (.reply _ _ _) hp, .vis hx h₁, h₂⟩
    | replyR q m n hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.runR q)
      rw [halves_inl_true]
      exact ⟨.cons (.reply _ _ _) hp, h₁, .vis hx h₂⟩
    | retL q r hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.idle false)
      erw [halves_retL]
      exact ⟨.cons (Step.ret (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inl q) r) hp, .vis hx h₁, h₂⟩
    | retR q r hx =>
      cases hb
      obtain ⟨hp, h₁, h₂⟩ := ih (SideOK.idle true)
      erw [halves_retR]
      exact ⟨.cons (Step.ret (E := E) (F := F₁ ⊕ₛ F₂) (Sum.inr q) r) hp, h₁, .vis hx h₂⟩

/-- A visible step of the left system, after silent steps, is a step of the pairing. -/
private theorem pair_vis₁ {L₁ : LTS E F₁} {L₂ : LTS E F₂} {p p₁ p' : Pos E (F₁ ⊕ₛ F₂)}
    {o : Move E (F₁ ⊕ₛ F₂)} {o₁ : Move E F₁} {s : List (Move E (F₁ ⊕ₛ F₂))}
    {s₁ : List (Move E F₁)} {x x' : L₁.State} {y y' : L₂.State}
    (hstep : ∀ {x₁ x₂}, L₁.step x₁ (some o₁) x₂ →
      LTS.PairStep L₁ L₂ (p, x₁, y) (some o) (p₁, x₂, y))
    (h₁ : L₁.Run x (o₁ :: s₁) x')
    (hrest : ∀ {x₂}, L₁.Run x₂ s₁ x' → (L₁.pair L₂).Run (p₁, x₂, y) s (p', x', y')) :
    (L₁.pair L₂).Run (p, x, y) (o :: s) (p', x', y') := by
  obtain ⟨x₁, x₂, ht, hst, hr⟩ := h₁.cons_inv
  exact LTS.Run.append (pair_taus₁ _ _ ht) (.vis (hstep hst) (hrest hr))

/-- A visible step of the right system, after silent steps, is a step of the pairing. -/
private theorem pair_vis₂ {L₁ : LTS E F₁} {L₂ : LTS E F₂} {p p₁ p' : Pos E (F₁ ⊕ₛ F₂)}
    {o : Move E (F₁ ⊕ₛ F₂)} {o₂ : Move E F₂} {s : List (Move E (F₁ ⊕ₛ F₂))}
    {s₂ : List (Move E F₂)} {x x' : L₁.State} {y y' : L₂.State}
    (hstep : ∀ {y₁ y₂}, L₂.step y₁ (some o₂) y₂ →
      LTS.PairStep L₁ L₂ (p, x, y₁) (some o) (p₁, x, y₂))
    (h₂ : L₂.Run y (o₂ :: s₂) y')
    (hrest : ∀ {y₂}, L₂.Run y₂ s₂ y' → (L₁.pair L₂).Run (p₁, x, y₂) s (p', x', y')) :
    (L₁.pair L₂).Run (p, x, y) (o :: s) (p', x', y') := by
  obtain ⟨y₁, y₂, ht, hst, hr⟩ := h₂.cons_inv
  exact LTS.Run.append (pair_taus₂ _ _ ht) (.vis (hstep hst) (hrest hr))

theorem run_pair {L₁ : LTS E F₁} {L₂ : LTS E F₂} {p p' : Pos E (F₁ ⊕ₛ F₂)}
    {s : List (Move E (F₁ ⊕ₛ F₂))} (h : Path p s p') :
    ∀ {b x x' y y'}, SideOK p b → L₁.Run x (halves b s).1 x' → L₂.Run y (halves b s).2 y' →
      (L₁.pair L₂).Run (p, x, y) s (p', x', y') := by
  induction h with
  | nil =>
    intro b x x' y y' _ h₁ h₂
    have h₁' : L₁.Run x [] x' := by simpa only [halves_nil] using h₁
    have h₂' : L₂.Run y [] y' := by simpa only [halves_nil] using h₂
    exact LTS.Run.append (pair_taus₁ _ _ h₁') (pair_taus₂ _ _ h₂')
  | @cons p p₁ p' o s st _ ih =>
    show ∀ {b x x' y y'}, SideOK p b → L₁.Run x (halves b (o :: s)).1 x' →
      L₂.Run y (halves b (o :: s)).2 y' → (L₁.pair L₂).Run (p, x, y) (o :: s) (p', x', y')
    intro b x x' y y' hb h₁ h₂
    cases st with
    | ask q =>
      show (L₁.pair L₂).Run (.idle, x, y) (.inr (.ask q) :: s) (p', x', y')
      rcases q with q | q
      · have h₁' : L₁.Run x (.inr (.ask q) :: (halves false s).1) x' := by
          simpa only [halves_askL] using h₁
        have h₂' : L₂.Run y (halves false s).2 y' := by simpa only [halves_askL] using h₂
        exact pair_vis₁ (LTS.PairStep.askL q) h₁' fun hr => ih (SideOK.runL q) hr h₂'
      · have h₁' : L₁.Run x (halves true s).1 x' := by simpa only [halves_askR] using h₁
        have h₂' : L₂.Run y (.inr (.ask q) :: (halves true s).2) y' := by
          simpa only [halves_askR] using h₂
        exact pair_vis₂ (LTS.PairStep.askR q) h₂' fun hr => ih (SideOK.runR q) h₁' hr
    | call q m =>
      rcases q with q | q <;> cases hb
      · exact pair_vis₁ (LTS.PairStep.callL q m) h₁ fun hr => ih (SideOK.waitL q m) hr h₂
      · exact pair_vis₂ (LTS.PairStep.callR q m) h₂ fun hr => ih (SideOK.waitR q m) h₁ hr
    | reply q m n =>
      rcases q with q | q <;> cases hb
      · exact pair_vis₁ (LTS.PairStep.replyL q m n) h₁ fun hr => ih (SideOK.runL q) hr h₂
      · exact pair_vis₂ (LTS.PairStep.replyR q m n) h₂ fun hr => ih (SideOK.runR q) h₁ hr
    | ret q r =>
      show (L₁.pair L₂).Run (.run q, x, y) (.inr (.ans q r) :: s) (p', x', y')
      rcases q with q | q <;> cases hb
      · have h₁' : L₁.Run x (.inr (.ans q r) :: (halves false s).1) x' :=
          h₁
        have h₂' : L₂.Run y (halves false s).2 y' := h₂
        exact pair_vis₁ (LTS.PairStep.retL q r) h₁' fun hr => ih (SideOK.idle false) hr h₂'
      · have h₁' : L₁.Run x (halves true s).1 x' := h₁
        have h₂' : L₂.Run y (.inr (.ans q r) :: (halves true s).2) y' :=
          h₂
        exact pair_vis₂ (LTS.PairStep.retR q r) h₂' fun hr => ih (SideOK.idle true) h₁' hr

theorem denotes_pair {L₁ : LTS E F₁} {L₂ : LTS E F₂} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    (h₁ : L₁.Denotes σ₁) (h₂ : L₂.Denotes σ₂) : (L₁.pair L₂).Denotes (σ₁.pair σ₂) := by
  intro p
  rw [Strategy.mem_pair]
  constructor
  · rintro ⟨z, h⟩
    obtain ⟨hp, hr₁, hr₂⟩ := pair_run h (SideOK.idle false)
    exact ⟨⟨_, hp⟩, (h₁ _).1 ⟨_, hr₁⟩, (h₂ _).1 ⟨_, hr₂⟩⟩
  · rintro ⟨⟨_, hp⟩, hs₁, hs₂⟩
    obtain ⟨x', hx⟩ := (h₁ _).2 hs₁
    obtain ⟨y', hy⟩ := (h₂ _).2 hs₂
    exact ⟨_, run_pair hp (SideOK.idle false) hx hy⟩

end Silmaril.Proofs.Games.Pair

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

theorem tstep_path {E F : Sig.{u}} {σ : Strategy E F} {x x' : List (Move E F)} {o : Move E F}
    {p : Pos E F} (h : σ.TStep x (some o) x') (hp : Path .idle x p) :
    ∃ p', Step p o p' ∧ Path .idle x' p' := by
  cases h with
  | mk _ hm =>
    obtain ⟨_, hl⟩ := σ.legal hm
    obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hl
    cases hy.det hp
    exact ⟨_, hst, hl⟩

end Silmaril.Proofs.Games.Pair
