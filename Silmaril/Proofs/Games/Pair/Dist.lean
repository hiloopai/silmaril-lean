module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Proofs.Games.Pair.LTS

/-!
# A handler below a pairing is duplicated: proofs

`ofHandler h ≫ (σ₁ ∥ σ₂) = (ofHandler h ≫ σ₁) ∥ (ofHandler h ≫ σ₂)`. The
transition systems of both sides simulate each other (`DistRel`): the handler
of the left-hand side runs exactly when the copy of the active side runs on the
right-hand side, and the inactive copy is idle. This uses that a handler keeps
no state between questions.
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

variable {E F F₁ F₂ : Sig.{u}}

/-- The transition system of `ofHandler h ≫ (σ₁ ∥ σ₂)`. -/
abbrev distL (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) : LTS E (F₁ ⊕ₛ F₂) :=
  h.toReduction.toLTS.comp (σ₁.toLTS.pair σ₂.toLTS)

/-- The transition system of `(ofHandler h ≫ σ₁) ∥ (ofHandler h ≫ σ₂)`. -/
abbrev distR (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) : LTS E (F₁ ⊕ₛ F₂) :=
  (h.toReduction.toLTS.comp σ₁.toLTS).pair (h.toReduction.toLTS.comp σ₂.toLTS)

/-- Corresponding states of the two sides. -/
inductive DistRel (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) :
    (distL h σ₁ σ₂).State → (distR h σ₁ σ₂).State → Prop
  | idle (x₁ : List (Move F F₁)) (x₂ : List (Move F F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ .idle →
      DistRel h σ₁ σ₂ (.idle, (.idle, x₁, x₂)) (.idle, (.idle, x₁), (.idle, x₂))
  | runL (q : F₁.Op) (x₁ : List (Move F F₁)) (x₂ : List (Move F F₂)) :
      Path .idle x₁ (.run q) → Path .idle x₂ .idle →
      DistRel h σ₁ σ₂ (.idle, (.run (Sum.inl q), x₁, x₂)) (.run (Sum.inl q), (.idle, x₁), (.idle, x₂))
  | callL (q : F₁.Op) (f : F.Op) (P : Prog E (F.Ar f)) (x₁ : List (Move F F₁))
      (x₂ : List (Move F F₂)) : Path .idle x₁ (.wait q f) → Path .idle x₂ .idle →
      DistRel h σ₁ σ₂ (.run f P, (.wait (Sum.inl q) f, x₁, x₂))
        (.run (Sum.inl q), (.run f P, x₁), (.idle, x₂))
  | waitL (q : F₁.Op) (f : F.Op) (e : E.Op) (k : E.Ar e → Prog E (F.Ar f))
      (x₁ : List (Move F F₁)) (x₂ : List (Move F F₂)) :
      Path .idle x₁ (.wait q f) → Path .idle x₂ .idle →
      DistRel h σ₁ σ₂ (.wait f e k, (.wait (Sum.inl q) f, x₁, x₂))
        (.wait (Sum.inl q) e, (.wait f e k, x₁), (.idle, x₂))
  | runR (q : F₂.Op) (x₁ : List (Move F F₁)) (x₂ : List (Move F F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ (.run q) →
      DistRel h σ₁ σ₂ (.idle, (.run (Sum.inr q), x₁, x₂)) (.run (Sum.inr q), (.idle, x₁), (.idle, x₂))
  | callR (q : F₂.Op) (f : F.Op) (P : Prog E (F.Ar f)) (x₁ : List (Move F F₁))
      (x₂ : List (Move F F₂)) : Path .idle x₁ .idle → Path .idle x₂ (.wait q f) →
      DistRel h σ₁ σ₂ (.run f P, (.wait (Sum.inr q) f, x₁, x₂))
        (.run (Sum.inr q), (.idle, x₁), (.run f P, x₂))
  | waitR (q : F₂.Op) (f : F.Op) (e : E.Op) (k : E.Ar e → Prog E (F.Ar f))
      (x₁ : List (Move F F₁)) (x₂ : List (Move F F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ (.wait q f) →
      DistRel h σ₁ σ₂ (.wait f e k, (.wait (Sum.inr q) f, x₁, x₂))
        (.wait (Sum.inr q) e, (.idle, x₁), (.wait f e k, x₂))

/-- The left-hand side is simulated by the right-hand side. -/
def distSim (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) :
    LTS.Simulation (distL h σ₁ σ₂) (distR h σ₁ σ₂) where
  R := DistRel h σ₁ σ₂
  init := .idle [] [] (.nil _) (.nil _)
  step := by
    intro z z' w l hr hs
    cases hr with
    | idle x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g hs =>
        cases hs with
        | askL q hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.PairStep.askL q (LTS.CompStep.right _ hx)) (.nil _),
            .runL q _ _ hp hp₂⟩
        | askR q hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.PairStep.askR q (LTS.CompStep.right _ hx)) (.nil _),
            .runR q _ _ hp₁ hp⟩
      | sync f hs ht => cases hs with | ask f => cases ht
    | runL q x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g hs =>
        cases hs with
        | retL q r hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.PairStep.retL q r (LTS.CompStep.right _ hx)) (.nil _),
            .idle _ _ hp hp₂⟩
      | sync f hs ht =>
        cases hs with
        | ask f =>
          cases ht with
          | callL q f hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _ (Reduction.Step.ask f) hx))
              (.nil _), .callL q f _ _ _ hp hp₂⟩
    | runR q x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g hs =>
        cases hs with
        | retR q r hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.PairStep.retR q r (LTS.CompStep.right _ hx)) (.nil _),
            .idle _ _ hp₁ hp⟩
      | sync f hs ht =>
        cases hs with
        | ask f =>
          cases ht with
          | callR q f hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ (Reduction.Step.ask f) hx))
              (.nil _), .callR q f _ _ _ hp₁ hp⟩
    | callL q f P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with | tau hc => exact (hc : False).elim
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | call hc =>
          cases hc
          exact ⟨_, .vis (LTS.PairStep.callL q _ (LTS.CompStep.left _
            (Reduction.Step.call (R := h.toReduction) rfl))) (.nil _), .waitL q f _ _ _ _ hp₁ hp₂⟩
      | right g hs => cases hs
      | sync f' hs ht =>
        cases hs with
        | ret hc =>
          cases hc
          cases ht with
          | replyL q f r hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _
              (Reduction.Step.ret (R := h.toReduction) rfl) hx)) (.nil _), .runL q _ _ hp hp₂⟩
    | callR q f P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with | tau hc => exact (hc : False).elim
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | call hc =>
          cases hc
          exact ⟨_, .vis (LTS.PairStep.callR q _ (LTS.CompStep.left _
            (Reduction.Step.call (R := h.toReduction) rfl))) (.nil _), .waitR q f _ _ _ _ hp₁ hp₂⟩
      | right g hs => cases hs
      | sync f' hs ht =>
        cases hs with
        | ret hc =>
          cases hc
          cases ht with
          | replyR q f r hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _
              (Reduction.Step.ret (R := h.toReduction) rfl) hx)) (.nil _), .runR q _ _ hp₁ hp⟩
    | waitL q f e k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e' hs =>
        cases hs with
        | resume _ _ _ n =>
          exact ⟨_, .vis (LTS.PairStep.replyL q e n (LTS.CompStep.left _
            (Reduction.Step.resume (R := h.toReduction) f e k n))) (.nil _),
            .callL q f _ _ _ hp₁ hp₂⟩
      | right g hs => cases hs
      | sync f' hs ht => cases hs
    | waitR q f e k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | left e' hs =>
        cases hs with
        | resume _ _ _ n =>
          exact ⟨_, .vis (LTS.PairStep.replyR q e n (LTS.CompStep.left _
            (Reduction.Step.resume (R := h.toReduction) f e k n))) (.nil _),
            .callR q f _ _ _ hp₁ hp₂⟩
      | right g hs => cases hs
      | sync f' hs ht => cases hs

/-- The right-hand side is simulated by the left-hand side. -/
def distSim' (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) :
    LTS.Simulation (distR h σ₁ σ₂) (distL h σ₁ σ₂) where
  R w z := DistRel h σ₁ σ₂ z w
  init := .idle [] [] (.nil _) (.nil _)
  step := by
    intro w w' z l hr hs
    cases hr with
    | idle x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | askL q hs =>
        cases hs with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askL q hx)) (.nil _),
            .runL q _ _ hp hp₂⟩
      | askR q hs =>
        cases hs with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askR q hx)) (.nil _),
            .runR q _ _ hp₁ hp⟩
    | runL q x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (Reduction.Step.ask f)
              (LTS.PairStep.callL q f hx)) (.nil _), .callL q f _ _ _ hp hp₂⟩
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | callL q m hs => cases hs with | left _ hh => cases hh
      | retL q r hs =>
        cases hs with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.retL q r hx)) (.nil _),
            .idle _ _ hp hp₂⟩
    | runR q x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (Reduction.Step.ask f)
              (LTS.PairStep.callR q f hx)) (.nil _), .callR q f _ _ _ hp₁ hp⟩
      | callR q m hs => cases hs with | left _ hh => cases hh
      | retR q r hs =>
        cases hs with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.retR q r hx)) (.nil _),
            .idle _ _ hp₁ hp⟩
    | callL q f P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs with | tau hc => exact (hc : False).elim
        | tau₂ hs => cases hs
        | sync f' hh hx =>
          cases hh with
          | ret hc =>
            cases hc
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (Reduction.Step.ret (R := h.toReduction) rfl)
              (LTS.PairStep.replyL q f _ hx)) (.nil _), .runL q _ _ hp hp₂⟩
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | callL q m hs =>
        cases hs with
        | left _ hh =>
          cases hh with
          | call hc =>
            cases hc
            exact ⟨_, .vis (LTS.CompStep.left _ (Reduction.Step.call (R := h.toReduction) rfl))
              (.nil _), .waitL q f _ _ _ _ hp₁ hp₂⟩
      | retL q r hs =>
        cases hs with
        | right _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
    | callR q f P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs with | tau hc => exact (hc : False).elim
        | tau₂ hs => cases hs
        | sync f' hh hx =>
          cases hh with
          | ret hc =>
            cases hc
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (Reduction.Step.ret (R := h.toReduction) rfl)
              (LTS.PairStep.replyR q f _ hx)) (.nil _), .runR q _ _ hp₁ hp⟩
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | callR q m hs =>
        cases hs with
        | left _ hh =>
          cases hh with
          | call hc =>
            cases hc
            exact ⟨_, .vis (LTS.CompStep.left _ (Reduction.Step.call (R := h.toReduction) rfl))
              (.nil _), .waitR q f _ _ _ _ hp₁ hp₂⟩
      | retR q r hs =>
        cases hs with
        | right _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
    | waitL q f e k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hh hx => cases hh
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | replyL q e n hs =>
        cases hs with
        | left _ hh =>
          cases hh with
          | resume _ _ _ n =>
            exact ⟨_, .vis (LTS.CompStep.left _
              (Reduction.Step.resume (R := h.toReduction) f e k n)) (.nil _),
              .callL q f _ _ _ hp₁ hp₂⟩
    | waitR q f e k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₂ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hh hx => cases hh
      | tau₁ hs =>
        cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hh hx =>
          cases hh with
          | ask f => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | replyR q e n hs =>
        cases hs with
        | left _ hh =>
          cases hh with
          | resume _ _ _ n =>
            exact ⟨_, .vis (LTS.CompStep.left _
              (Reduction.Step.resume (R := h.toReduction) f e k n)) (.nil _),
              .callR q f _ _ _ hp₁ hp₂⟩

theorem ofHandler_comp_pair (h : Handler E F) (σ₁ : Strategy F F₁) (σ₂ : Strategy F F₂) :
    (Strategy.ofHandler h).comp (σ₁.pair σ₂) =
      ((Strategy.ofHandler h).comp σ₁).pair ((Strategy.ofHandler h).comp σ₂) :=
  LTS.Denotes.eq_of_simulation
    ((Handler.denotes_toLTS h).comp (denotes_pair σ₁.denotes_toLTS σ₂.denotes_toLTS))
    (denotes_pair ((Handler.denotes_toLTS h).comp σ₁.denotes_toLTS)
      ((Handler.denotes_toLTS h).comp σ₂.denotes_toLTS))
    (distSim h σ₁ σ₂) (distSim' h σ₁ σ₂)

end Silmaril.Proofs.Games.Pair
