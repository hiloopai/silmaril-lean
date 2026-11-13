module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Proofs.Games.Pair.LTS

/-!
# The pairing of two handlers is the handler of their copairing: proofs

The transition systems of `copair h₁ h₂` and of the pairing of those of `h₁`
and `h₂` simulate each other (`CpRel`).
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- States of the copaired handler and of the pairing of the two handlers. -/
inductive CpRel (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    (Handler.copair h₁ h₂).toReduction.toLTS.State →
    (h₁.toReduction.toLTS.pair h₂.toReduction.toLTS).State → Prop
  | idle : CpRel h₁ h₂ .idle (.idle, .idle, .idle)
  | runL (q : F₁.Op) (P : Prog E (F₁.Ar q)) :
      CpRel h₁ h₂ (.run (Sum.inl q) P) (.run (Sum.inl q), .run q P, .idle)
  | waitL (q : F₁.Op) (m : E.Op) (k : E.Ar m → Prog E (F₁.Ar q)) :
      CpRel h₁ h₂ (.wait (Sum.inl q) m k) (.wait (Sum.inl q) m, .wait q m k, .idle)
  | runR (q : F₂.Op) (P : Prog E (F₂.Ar q)) :
      CpRel h₁ h₂ (.run (Sum.inr q) P) (.run (Sum.inr q), .idle, .run q P)
  | waitR (q : F₂.Op) (m : E.Op) (k : E.Ar m → Prog E (F₂.Ar q)) :
      CpRel h₁ h₂ (.wait (Sum.inr q) m k) (.wait (Sum.inr q) m, .idle, .wait q m k)

/-- The copaired handler is simulated by the pairing. -/
def cpSim (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    LTS.Simulation (Handler.copair h₁ h₂).toReduction.toLTS
      (h₁.toReduction.toLTS.pair h₂.toReduction.toLTS) where
  R := CpRel h₁ h₂
  init := .idle
  step := by
    intro x x' y l hr hs
    cases hs with
    | ask q =>
      cases hr
      rcases q with q | q
      · exact ⟨_, .vis (LTS.PairStep.askL q (Reduction.Step.ask q)) (.nil _), .runL q (h₁ q)⟩
      · exact ⟨_, .vis (LTS.PairStep.askR q (Reduction.Step.ask q)) (.nil _), .runR q (h₂ q)⟩
    | tau hc => exact (hc : False).elim
    | call hc =>
      cases hr with
      | runL q P =>
        cases hc
        exact ⟨_, .vis (LTS.PairStep.callL q _ (Reduction.Step.call rfl)) (.nil _), .waitL _ _ _⟩
      | runR q P =>
        cases hc
        exact ⟨_, .vis (LTS.PairStep.callR q _ (Reduction.Step.call rfl)) (.nil _), .waitR _ _ _⟩
    | resume q m k n =>
      cases hr with
      | waitL q m k =>
        exact ⟨_, .vis (LTS.PairStep.replyL q m n (Reduction.Step.resume _ _ _ n)) (.nil _),
          .runL _ _⟩
      | waitR q m k =>
        exact ⟨_, .vis (LTS.PairStep.replyR q m n (Reduction.Step.resume _ _ _ n)) (.nil _),
          .runR _ _⟩
    | ret hc =>
      cases hr with
      | runL q P =>
        cases hc
        exact ⟨_, .vis (LTS.PairStep.retL q _ (Reduction.Step.ret rfl)) (.nil _), .idle⟩
      | runR q P =>
        cases hc
        exact ⟨_, .vis (LTS.PairStep.retR q _ (Reduction.Step.ret rfl)) (.nil _), .idle⟩

/-- The pairing is simulated by the copaired handler. -/
def cpSim' (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    LTS.Simulation (h₁.toReduction.toLTS.pair h₂.toReduction.toLTS)
      (Handler.copair h₁ h₂).toReduction.toLTS where
  R y x := CpRel h₁ h₂ x y
  init := .idle
  step := by
    intro y y' x l hr hs
    cases hs with
    | tau₁ hs => cases hs with | tau hc => exact (hc : False).elim
    | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
    | askL q hx =>
      cases hr
      cases hx
      exact ⟨_, .vis (Reduction.Step.ask (R := (Handler.copair h₁ h₂).toReduction) (Sum.inl q)) (.nil _), .runL q (h₁ q)⟩
    | askR q hx =>
      cases hr
      cases hx
      exact ⟨_, .vis (Reduction.Step.ask (R := (Handler.copair h₁ h₂).toReduction) (Sum.inr q)) (.nil _), .runR q (h₂ q)⟩
    | callL q m hx =>
      cases hr with
      | runL q P =>
        cases hx with
        | call hc =>
          cases hc
          exact ⟨_, .vis (Reduction.Step.call rfl) (.nil _), .waitL _ _ _⟩
    | callR q m hx =>
      cases hr with
      | runR q P =>
        cases hx with
        | call hc =>
          cases hc
          exact ⟨_, .vis (Reduction.Step.call rfl) (.nil _), .waitR _ _ _⟩
    | replyL q m n hx =>
      cases hr with
      | waitL q m k =>
        cases hx
        exact ⟨_, .vis (Reduction.Step.resume _ _ _ n) (.nil _), .runL _ _⟩
    | replyR q m n hx =>
      cases hr with
      | waitR q m k =>
        cases hx
        exact ⟨_, .vis (Reduction.Step.resume _ _ _ n) (.nil _), .runR _ _⟩
    | retL q r hx =>
      cases hr with
      | runL q P =>
        cases hx with
        | ret hc =>
          cases hc
          exact ⟨_, .vis (Reduction.Step.ret rfl) (.nil _), .idle⟩
    | retR q r hx =>
      cases hr with
      | runR q P =>
        cases hx with
        | ret hc =>
          cases hc
          exact ⟨_, .vis (Reduction.Step.ret rfl) (.nil _), .idle⟩

theorem ofHandler_pair_ofHandler (h₁ : Handler E F₁) (h₂ : Handler E F₂) :
    (Strategy.ofHandler h₁).pair (Strategy.ofHandler h₂) =
      Strategy.ofHandler (Handler.copair h₁ h₂) :=
  LTS.Denotes.eq_of_simulation
    (denotes_pair (Handler.denotes_toLTS h₁) (Handler.denotes_toLTS h₂))
    (Handler.denotes_toLTS _) (cpSim' h₁ h₂) (cpSim h₁ h₂)

end Silmaril.Proofs.Games.Pair
