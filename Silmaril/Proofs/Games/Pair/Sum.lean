module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Proofs.Games.Pair.LTS

/-!
# A sum of handlers above a pairing acts side by side: proofs

`(σ₁ ∥ σ₂) ≫ ofHandler (sumMap h₁ h₂) = (σ₁ ≫ ofHandler h₁) ∥ (σ₂ ≫ ofHandler h₂)`.
The two transition systems simulate each other (`SumRel`): the sum handler
runs `P.interp ι` exactly when the handler of the active side runs `P`.
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

variable {E F₁ F₂ G₁ G₂ : Sig.{u}}

/-- The transition system of `(σ₁ ∥ σ₂) ≫ ofHandler (sumMap h₁ h₂)`. -/
abbrev sumL (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) : LTS E (G₁ ⊕ₛ G₂) :=
  (σ₁.toLTS.pair σ₂.toLTS).comp (Handler.sumMap h₁ h₂).toReduction.toLTS

/-- The transition system of `(σ₁ ≫ ofHandler h₁) ∥ (σ₂ ≫ ofHandler h₂)`. -/
abbrev sumR (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) : LTS E (G₁ ⊕ₛ G₂) :=
  (σ₁.toLTS.comp h₁.toReduction.toLTS).pair (σ₂.toLTS.comp h₂.toReduction.toLTS)

/-- The left and right injections as handlers. -/
abbrev ιL (F₁ F₂ : Sig.{u}) : Handler (F₁ ⊕ₛ F₂) F₁ := Handler.ofHom (Sig.Hom.inl F₁ F₂)
/-- The right injection as a handler. -/
abbrev ιR (F₁ F₂ : Sig.{u}) : Handler (F₁ ⊕ₛ F₂) F₂ := Handler.ofHom (Sig.Hom.inr F₁ F₂)

/-- Corresponding states of the two sides. -/
inductive SumRel (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) : (sumL σ₁ σ₂ h₁ h₂).State → (sumR σ₁ σ₂ h₁ h₂).State → Prop
  | idle (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ .idle →
      SumRel σ₁ σ₂ h₁ h₂ ((.idle, x₁, x₂), .idle) (.idle, (x₁, .idle), (x₂, .idle))
  | runL (g : G₁.Op) (P : Prog F₁ (G₁.Ar g)) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ .idle →
      SumRel σ₁ σ₂ h₁ h₂ ((.idle, x₁, x₂), .run (Sum.inl g) (P.interp (ιL F₁ F₂)))
        (.run (Sum.inl g), (x₁, .run g P), (x₂, .idle))
  | callL (g : G₁.Op) (f : F₁.Op) (k : F₁.Ar f → Prog F₁ (G₁.Ar g)) (x₁ : List (Move E F₁))
      (x₂ : List (Move E F₂)) : Path .idle x₁ (.run f) → Path .idle x₂ .idle →
      SumRel σ₁ σ₂ h₁ h₂
        ((.run (Sum.inl f), x₁, x₂), .wait (Sum.inl g) (Sum.inl f) fun n => (k n).interp (ιL F₁ F₂))
        (.run (Sum.inl g), (x₁, .wait g f k), (x₂, .idle))
  | waitL (g : G₁.Op) (f : F₁.Op) (k : F₁.Ar f → Prog F₁ (G₁.Ar g)) (e : E.Op)
      (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) :
      Path .idle x₁ (.wait f e) → Path .idle x₂ .idle →
      SumRel σ₁ σ₂ h₁ h₂
        ((.wait (Sum.inl f) e, x₁, x₂), .wait (Sum.inl g) (Sum.inl f) fun n => (k n).interp (ιL F₁ F₂))
        (.wait (Sum.inl g) e, (x₁, .wait g f k), (x₂, .idle))
  | runR (g : G₂.Op) (P : Prog F₂ (G₂.Ar g)) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ .idle →
      SumRel σ₁ σ₂ h₁ h₂ ((.idle, x₁, x₂), .run (Sum.inr g) (P.interp (ιR F₁ F₂)))
        (.run (Sum.inr g), (x₁, .idle), (x₂, .run g P))
  | callR (g : G₂.Op) (f : F₂.Op) (k : F₂.Ar f → Prog F₂ (G₂.Ar g)) (x₁ : List (Move E F₁))
      (x₂ : List (Move E F₂)) : Path .idle x₁ .idle → Path .idle x₂ (.run f) →
      SumRel σ₁ σ₂ h₁ h₂
        ((.run (Sum.inr f), x₁, x₂), .wait (Sum.inr g) (Sum.inr f) fun n => (k n).interp (ιR F₁ F₂))
        (.run (Sum.inr g), (x₁, .idle), (x₂, .wait g f k))
  | waitR (g : G₂.Op) (f : F₂.Op) (k : F₂.Ar f → Prog F₂ (G₂.Ar g)) (e : E.Op)
      (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) :
      Path .idle x₁ .idle → Path .idle x₂ (.wait f e) →
      SumRel σ₁ σ₂ h₁ h₂
        ((.wait (Sum.inr f) e, x₁, x₂), .wait (Sum.inr g) (Sum.inr f) fun n => (k n).interp (ιR F₁ F₂))
        (.wait (Sum.inr g) e, (x₁, .idle), (x₂, .wait g f k))

/-- The left-hand side is simulated by the right-hand side. -/
def sumSim (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁) (h₂ : Handler F₂ G₂) :
    LTS.Simulation (sumL σ₁ σ₂ h₁ h₂) (sumR σ₁ σ₂ h₁ h₂) where
  R := SumRel σ₁ σ₂ h₁ h₂
  init := .idle [] [] (.nil _) (.nil _)
  step := by
    intro z z' w l hr hs
    cases hr with
    | idle x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g hs =>
        cases hs with
        | ask g =>
          rcases g with g | g
          · exact ⟨_, .vis (LTS.PairStep.askL g (LTS.CompStep.right _ (Reduction.Step.ask g)))
              (.nil _), .runL g (h₁ g) _ _ hp₁ hp₂⟩
          · exact ⟨_, .vis (LTS.PairStep.askR g (LTS.CompStep.right _ (Reduction.Step.ask g)))
              (.nil _), .runR g (h₂ g) _ _ hp₁ hp₂⟩
      | sync f hs ht => cases ht
    | runL g P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
      | left e hs => cases hs
      | right g' hs =>
        cases hs with
        | ret hc =>
          cases P with
          | pure r =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.retL g _ (LTS.CompStep.right _
              (Reduction.Step.ret (R := h₁.toReduction) rfl))) (.nil _), .idle _ _ hp₁ hp₂⟩
          | call f k => cases hc
      | sync f' hs ht =>
        cases ht with
        | call hc =>
          cases P with
          | pure r => cases hc
          | call f k =>
            cases hc
            cases hs with
            | askL f hx =>
              obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
              cases hst
              exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _ hx
                (Reduction.Step.call (R := h₁.toReduction) rfl))) (.nil _),
                .callL g f k _ _ hp hp₂⟩
    | runR g P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
      | left e hs => cases hs
      | right g' hs =>
        cases hs with
        | ret hc =>
          cases P with
          | pure r =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.retR g _ (LTS.CompStep.right _
              (Reduction.Step.ret (R := h₂.toReduction) rfl))) (.nil _), .idle _ _ hp₁ hp₂⟩
          | call f k => cases hc
      | sync f' hs ht =>
        cases ht with
        | call hc =>
          cases P with
          | pure r => cases hc
          | call f k =>
            cases hc
            cases hs with
            | askR f hx =>
              obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
              cases hst
              exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ hx
                (Reduction.Step.call (R := h₂.toReduction) rfl))) (.nil _),
                .callR g f k _ _ hp₁ hp⟩
    | callL g f k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | callL f m hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.PairStep.callL g m (LTS.CompStep.left _ hx)) (.nil _),
            .waitL g f k m _ _ hp hp₂⟩
      | right g' hs => cases hs
      | sync f' hs ht =>
        cases ht with
        | resume _ _ _ r =>
          cases hs with
          | retL f r hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _ hx
              (Reduction.Step.resume (R := h₁.toReduction) g f k r))) (.nil _),
              .runL g (k r) _ _ hp hp₂⟩
    | callR g f k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | callR f m hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.PairStep.callR g m (LTS.CompStep.left _ hx)) (.nil _),
            .waitR g f k m _ _ hp₁ hp⟩
      | right g' hs => cases hs
      | sync f' hs ht =>
        cases ht with
        | resume _ _ _ r =>
          cases hs with
          | retR f r hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ hx
              (Reduction.Step.resume (R := h₂.toReduction) g f k r))) (.nil _),
              .runR g (k r) _ _ hp₁ hp⟩
    | waitL g f k e x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e' hs =>
        cases hs with
        | replyL f e n hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.PairStep.replyL g e n (LTS.CompStep.left _ hx)) (.nil _),
            .callL g f k _ _ hp hp₂⟩
      | right g' hs => cases hs
      | sync f' hs ht =>
        cases ht with
        | resume _ _ _ r => cases hs
    | waitR g f k e x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e' hs =>
        cases hs with
        | replyR f e n hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.PairStep.replyR g e n (LTS.CompStep.left _ hx)) (.nil _),
            .callR g f k _ _ hp₁ hp⟩
      | right g' hs => cases hs
      | sync f' hs ht =>
        cases ht with
        | resume _ _ _ r => cases hs

/-- The right-hand side is simulated by the left-hand side. -/
def sumSim' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁) (h₂ : Handler F₂ G₂) :
    LTS.Simulation (sumR σ₁ σ₂ h₁ h₂) (sumL σ₁ σ₂ h₁ h₂) where
  R w z := SumRel σ₁ σ₂ h₁ h₂ z w
  init := .idle [] [] (.nil _) (.nil _)
  step := by
    intro w w' z l hr hs
    cases hr with
    | idle x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | askL g hs =>
        cases hs with
        | right _ hh =>
          cases hh
          exact ⟨_, .vis (LTS.CompStep.right _
            (Reduction.Step.ask (R := (Handler.sumMap h₁ h₂).toReduction) (Sum.inl g))) (.nil _),
            .runL g (h₁ g) _ _ hp₁ hp₂⟩
      | askR g hs =>
        cases hs with
        | right _ hh =>
          cases hh
          exact ⟨_, .vis (LTS.CompStep.right _
            (Reduction.Step.ask (R := (Handler.sumMap h₁ h₂).toReduction) (Sum.inr g))) (.nil _),
            .runR g (h₂ g) _ _ hp₁ hp₂⟩
    | runL g P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
        | sync f hx hh =>
          cases hh with
          | call hc =>
            cases hc
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.askL _ hx)
              (Reduction.Step.call (R := (Handler.sumMap h₁ h₂).toReduction) rfl)) (.nil _),
              .callL g _ _ _ _ hp hp₂⟩
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | callL g m hs =>
        cases hs with
        | left _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | retL g r hs =>
        cases hs with
        | right _ hh =>
          cases hh with
          | ret hc =>
            cases hc
            exact ⟨_, .vis (LTS.CompStep.right _
              (Reduction.Step.ret (R := (Handler.sumMap h₁ h₂).toReduction) rfl)) (.nil _),
              .idle _ _ hp₁ hp₂⟩
    | runR g P x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
        | sync f hx hh =>
          cases hh with
          | call hc =>
            cases hc
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.askR _ hx)
              (Reduction.Step.call (R := (Handler.sumMap h₁ h₂).toReduction) rfl)) (.nil _),
              .callR g _ _ _ _ hp₁ hp⟩
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | callR g m hs =>
        cases hs with
        | left _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | retR g r hs =>
        cases hs with
        | right _ hh =>
          cases hh with
          | ret hc =>
            cases hc
            exact ⟨_, .vis (LTS.CompStep.right _
              (Reduction.Step.ret (R := (Handler.sumMap h₁ h₂).toReduction) rfl)) (.nil _),
              .idle _ _ hp₁ hp₂⟩
    | callL g f k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hx hh =>
          cases hh with
          | resume _ _ _ r =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retL f r hx)
              (Reduction.Step.resume (R := (Handler.sumMap h₁ h₂).toReduction) (Sum.inl g)
                (Sum.inl f) (fun n => (k n).interp (ιL F₁ F₂)) r)) (.nil _),
              .runL g (k r) _ _ hp hp₂⟩
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | callL g m hs =>
        cases hs with
        | left _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callL f m hx)) (.nil _),
            .waitL g f k m _ _ hp hp₂⟩
      | retL g r hs => cases hs with | right _ hh => cases hh
    | callR g f k x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hx hh =>
          cases hh with
          | resume _ _ _ r =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retR f r hx)
              (Reduction.Step.resume (R := (Handler.sumMap h₁ h₂).toReduction) (Sum.inr g)
                (Sum.inr f) (fun n => (k n).interp (ιR F₁ F₂)) r)) (.nil _),
              .runR g (k r) _ _ hp₁ hp⟩
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | callR g m hs =>
        cases hs with
        | left _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callR f m hx)) (.nil _),
            .waitR g f k m _ _ hp₁ hp⟩
      | retR g r hs => cases hs with | right _ hh => cases hh
    | waitL g f k e x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hx hh =>
          cases hh with
          | resume _ _ _ r => obtain ⟨_, hst, -⟩ := tstep_path hx hp₁; cases hst
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | replyL g e n hs =>
        cases hs with
        | left _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₁
          cases hst
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyL f e n hx)) (.nil _),
            .callL g f k _ _ hp hp₂⟩
    | waitR g f k e x₁ x₂ hp₁ hp₂ =>
      cases hs with
      | tau₂ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f' hx hh =>
          cases hh with
          | resume _ _ _ r => obtain ⟨_, hst, -⟩ := tstep_path hx hp₂; cases hst
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
        | sync f hx hh => cases hh
      | replyR g e n hs =>
        cases hs with
        | left _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hp₂
          cases hst
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyR f e n hx)) (.nil _),
            .callR g f k _ _ hp₁ hp⟩

theorem pair_comp_sumMap (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (h₁ : Handler F₁ G₁)
    (h₂ : Handler F₂ G₂) :
    (σ₁.pair σ₂).comp (Strategy.ofHandler (Handler.sumMap h₁ h₂)) =
      (σ₁.comp (Strategy.ofHandler h₁)).pair (σ₂.comp (Strategy.ofHandler h₂)) :=
  LTS.Denotes.eq_of_simulation
    ((denotes_pair σ₁.denotes_toLTS σ₂.denotes_toLTS).comp (Handler.denotes_toLTS _))
    (denotes_pair (σ₁.denotes_toLTS.comp (Handler.denotes_toLTS h₁))
      (σ₂.denotes_toLTS.comp (Handler.denotes_toLTS h₂)))
    (sumSim σ₁ σ₂ h₁ h₂) (sumSim' σ₁ σ₂ h₁ h₂)

end Silmaril.Proofs.Games.Pair
