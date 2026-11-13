module

public import Silmaril.Proofs.Wasm.Component.Reference.Games

/-!
# Plays of several answered questions through compositions, handlers and pairings

The multi-question versions of the two-move lemmas of `Games`. A *round* is a question with
its answer, and `twos l` is the play answering the rounds `l` one after another, with no lower
moves. Strategies keep state between questions, so membership of `twos l` is not a property of
the single rounds; it is propagated through the layers:

* handlers (`twos_comp_ofHandler`): `HRounds h up low` says that the handler `h` answers each
  upper round of `up` at once or by one call, the calls being the rounds `low`; a play of `low`
  below gives the play of `up` above (handlers keep no state, so the handler's own play is the
  concatenation of its rounds);
* compositions without calls (`twos_comp_upper`);
* pairing (`twos_pair_inr`): rounds of the right component;
* legality (`legal_twos`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games

universe u

variable {E F G : Sig.{u}}

/-- A question with its answer. -/
abbrev Round (F : Sig.{u}) : Type u := Σ q : F.Op, F.Ar q

/-- The play answering the rounds `l` one after another. -/
def twos : List (Round F) → List (Move E F)
  | [] => []
  | ⟨q, a⟩ :: l => .inr (.ask q) :: .inr (.ans q a) :: twos l

@[simp] theorem twos_nil : twos ([] : List (Round F)) = ([] : List (Move E F)) := rfl

theorem twos_cons (q : F.Op) (a : F.Ar q) (l : List (Round F)) :
    twos (E := E) (⟨q, a⟩ :: l) = two q a ++ twos l := rfl

theorem twos_append : ∀ (l l' : List (Round F)),
    twos (E := E) (l ++ l') = twos l ++ twos l'
  | [], _ => rfl
  | ⟨q, a⟩ :: l, l' => by
    show two q a ++ twos (l ++ l') = (two q a ++ twos l) ++ twos l'
    rw [twos_append l l', List.append_assoc]

theorem twos_singleton (q : F.Op) (a : F.Ar q) : twos (E := E) [⟨q, a⟩] = two q a := rfl

/-- The automaton reads complete rounds from idle to idle. -/
theorem path_twos : ∀ (l : List (Round F)), Path (E := E) .idle (twos l) .idle
  | [] => .nil _
  | ⟨q, a⟩ :: l => .cons (.ask q) (.cons (.ret q a) (path_twos l))

theorem legal_twos (l : List (Round F)) : Legal (twos (E := E) l) := ⟨_, path_twos l⟩

/-! ## Zips -/

theorem zip_append {α β γ : Type u} {s s' : List (α ⊕ β)} {t t' : List (β ⊕ γ)}
    {p p' : List (α ⊕ γ)} (h : Zip s t p) (h' : Zip s' t' p') :
    Zip (s ++ s') (t ++ t') (p ++ p') := by
  induction h with
  | nil => exact h'
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

/-- Rounds without lower moves interact with the empty lower play. -/
theorem zip_nil_twos : ∀ (l : List (Round G)),
    Zip ([] : List (Move E F)) (twos (E := F) l) (twos (E := E) l)
  | [] => .nil
  | ⟨_, _⟩ :: l => .right _ (.right _ (zip_nil_twos l))

/-- **Composition without calls**, for several rounds. -/
theorem twos_comp_upper {σ : Strategy E F} {τ : Strategy F G} {l : List (Round G)}
    (hτ : twos l ∈ τ) : twos l ∈ σ.comp τ :=
  ⟨[], σ.nil_mem, _, hτ, zip_nil_twos l⟩

/-! ## Handlers -/

/-- `HRounds h up low`: the handler `h` answers the rounds `up`, each at once (`pure`) or by
one call (`call`), the calls and their answers being the rounds `low`, in order. -/
inductive HRounds (h : Handler F G) : List (Round G) → List (Round F) → Prop
  | nil : HRounds h [] []
  | pure {q : G.Op} {a : G.Ar q} {up : List (Round G)} {low : List (Round F)} :
      h q = .pure a → HRounds h up low → HRounds h (⟨q, a⟩ :: up) low
  | call {q : G.Op} {q' : F.Op} {k : F.Ar q' → Prog F (G.Ar q)} {a' : F.Ar q'} {a : G.Ar q}
      {up : List (Round G)} {low : List (Round F)} :
      h q = .call q' k → k a' = .pure a → HRounds h up low →
      HRounds h (⟨q, a⟩ :: up) (⟨q', a'⟩ :: low)

theorem HRounds.append {h : Handler F G} {up up' : List (Round G)} {low low' : List (Round F)}
    (H : HRounds h up low) (H' : HRounds h up' low') : HRounds h (up ++ up') (low ++ low') := by
  induction H with
  | nil => exact H'
  | pure hq _ ih => exact .pure hq ih
  | call hq hk _ ih => exact .call hq hk ih

/-- The handler's own play of `HRounds h up low`: complete runs of its reduction semantics,
from idle to idle, interacting with `twos low` to give `twos up`. -/
theorem HRounds.run {h : Handler F G} {up : List (Round G)} {low : List (Round F)}
    (H : HRounds h up low) :
    ∃ t, h.toReduction.toLTS.Run .idle t .idle ∧ Zip (twos (E := E) low) t (twos up) := by
  induction H with
  | nil => exact ⟨[], .nil _, .nil⟩
  | @pure q a _ _ hq _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    refine ⟨.inr (.ask q) :: .inr (.ans q a) :: t, ?_, .right _ (.right _ hz)⟩
    exact .vis (.ask q) (.vis (.ret (show h q = .pure a from hq)) ht)
  | @call q q' k a' a _ _ hq hk _ ih =>
    obtain ⟨t, ht, hz⟩ := ih
    refine ⟨.inr (.ask q) :: .inl (.ask q') :: .inl (.ans q' a') :: .inr (.ans q a) :: t, ?_,
      .right _ (.sync _ (.sync _ (.right _ hz)))⟩
    exact .vis (.ask q) (.vis (.call (show h q = .call q' k from hq))
      (.vis (Reduction.Step.resume (R := h.toReduction) q q' k a')
        (.vis (.ret (show k a' = .pure a from hk)) ht)))

/-- **A handler on top**, for several rounds: the rounds `up` that `h` answers from the rounds
`low` of the strategy below. -/
theorem twos_comp_ofHandler {σ : Strategy E F} {h : Handler F G} {up : List (Round G)}
    {low : List (Round F)} (H : HRounds h up low) (hσ : twos low ∈ σ) :
    twos up ∈ σ.comp (Strategy.ofHandler h) := by
  obtain ⟨t, ht, hz⟩ := H.run (E := E)
  exact ⟨_, hσ, t, Strategy.mem_ofHandler.mpr ⟨_, ht⟩, hz⟩

/-- A handler forwarding every round by one call: each round `x` of `low` is the call of the
round `f x` of `up`. -/
theorem hrounds_map {h : Handler F G} (f : Round F → Round G) :
    ∀ (low : List (Round F)),
      (∀ x ∈ low, ∃ k, h (f x).1 = .call x.1 k ∧ k x.2 = .pure (f x).2) →
      HRounds h (low.map f) low
  | [], _ => .nil
  | x :: low, hf => by
    obtain ⟨k, hq, hk⟩ := hf x List.mem_cons_self
    exact .call hq hk (hrounds_map f low fun y hy => hf y (List.mem_cons_of_mem _ hy))

/-! ## Pairing -/

/-- A round of the right component of a pairing. -/
def Round.inr {F₁ F₂ : Sig.{u}} (x : Round F₂) : Round (F₁ ⊕ₛ F₂) := ⟨.inr x.1, x.2⟩

theorem halves_twos_inr {F₁ F₂ : Sig.{u}} :
    ∀ (b : Bool) (l : List (Round F₂)),
      Split.halves b (twos (E := E) (l.map (Round.inr (F₁ := F₁)))) = ([], twos l)
  | _, [] => rfl
  | b, ⟨q, a⟩ :: l => by
    show Split.halves b (.inr (.ask (.inr q)) :: .inr (.ans (.inr q) a) ::
      twos (l.map (Round.inr (F₁ := F₁)))) = _
    simp only [Split.halves, halves_twos_inr true l]
    rfl

/-- **Rounds of the right component of a pairing.** -/
theorem twos_pair_inr {F₁ F₂ : Sig.{u}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {l : List (Round F₂)} (h : twos l ∈ σ₂) :
    twos (l.map (Round.inr (F₁ := F₁))) ∈ σ₁.pair σ₂ := by
  refine ⟨legal_twos _, ?_, ?_⟩
  · rw [halves_twos_inr]
    exact σ₁.nil_mem
  · rw [halves_twos_inr]
    exact h

end Silmaril.Proofs.Wasm.Component.Reference
