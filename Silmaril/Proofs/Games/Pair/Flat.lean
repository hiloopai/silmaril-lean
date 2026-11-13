module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Proofs.Games.Pair.LTS
public import Silmaril.Proofs.Games.Pair.Proj

/-!
# Re-associating a pairing with a stateless left component: proofs

For a handler `h`,
`(h ∥ σ) ≫ (fst ∥ τ) = h ∥ ((h ∥ σ) ≫ τ)`, where `fst` forwards `F₁` to the
left of `F₁ ⊕ₛ F₂`. On the left, the questions in `F₁` are forwarded to the
copy of `h` inside `h ∥ σ`, which `τ` also uses; on the right they go to a
separate copy of `h`. Since `h` keeps no state the two agree. The transition
systems simulate each other (`FlatRel`); the forwarding may hold a question or
an answer for one silent step (`FlatRel.fwd`, `FlatRel.back`), which the
reverse simulation avoids by forwarding eagerly.
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

variable {E F₁ F₂ G : Sig.{u}}

/-- The transition system of `h ∥ σ`. -/
abbrev flatA (h : Handler E F₁) (σ : Strategy E F₂) : LTS E (F₁ ⊕ₛ F₂) :=
  h.toReduction.toLTS.pair σ.toLTS

/-- The transition system of `(h ∥ σ) ≫ (fst ∥ τ)`. -/
abbrev flatL (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    LTS E (F₁ ⊕ₛ G) :=
  (flatA h σ).comp ((fstH F₁ F₂).toReduction.toLTS.pair τ.toLTS)

/-- The transition system of `h ∥ ((h ∥ σ) ≫ τ)`. -/
abbrev flatR (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    LTS E (F₁ ⊕ₛ G) :=
  h.toReduction.toLTS.pair ((flatA h σ).comp τ.toLTS)

/-- Corresponding states. The constructors `fwd` and `back` are only used
from left to right. -/
inductive FlatRel (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    Bool → (flatL h σ τ).State → (flatR h σ τ).State → Prop
  | idle (b : Bool) (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) :
      Path .idle xτ .idle →
      FlatRel h σ τ b ((.idle, .idle, xσ), (.idle, .idle, xτ))
        (.idle, .idle, ((.idle, .idle, xσ), xτ))
  | fwd (q : F₁.Op) (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) :
      Path .idle xτ .idle →
      FlatRel h σ τ true ((.idle, .idle, xσ), (.run (Sum.inl q), .run q (fstH F₁ F₂ q), xτ))
        (.run (Sum.inl q), .run q (h q), ((.idle, .idle, xσ), xτ))
  | hrun (b : Bool) (q : F₁.Op) (P : Prog E (F₁.Ar q)) (xσ : List (Move E F₂))
      (xτ : List (Move (F₁ ⊕ₛ F₂) G)) : Path .idle xτ .idle →
      FlatRel h σ τ b ((.run (Sum.inl q), .run q P, xσ),
          (.wait (Sum.inl q) (Sum.inl q), .wait q (Sum.inl q) fun n => .pure n, xτ))
        (.run (Sum.inl q), .run q P, ((.idle, .idle, xσ), xτ))
  | hwait (b : Bool) (q : F₁.Op) (e : E.Op) (k : E.Ar e → Prog E (F₁.Ar q))
      (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) : Path .idle xτ .idle →
      FlatRel h σ τ b ((.wait (Sum.inl q) e, .wait q e k, xσ),
          (.wait (Sum.inl q) (Sum.inl q), .wait q (Sum.inl q) fun n => .pure n, xτ))
        (.wait (Sum.inl q) e, .wait q e k, ((.idle, .idle, xσ), xτ))
  | back (q : F₁.Op) (r : F₁.Ar q) (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) :
      Path .idle xτ .idle →
      FlatRel h σ τ true ((.idle, .idle, xσ), (.run (Sum.inl q), .run q (.pure r), xτ))
        (.run (Sum.inl q), .run q (.pure r), ((.idle, .idle, xσ), xτ))
  | grun (b : Bool) (g : G.Op) (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) :
      Path .idle xτ (.run g) →
      FlatRel h σ τ b ((.idle, .idle, xσ), (.run (Sum.inr g), .idle, xτ))
        (.run (Sum.inr g), .idle, ((.idle, .idle, xσ), xτ))
  | chrun (b : Bool) (g : G.Op) (q : F₁.Op) (P : Prog E (F₁.Ar q)) (xσ : List (Move E F₂))
      (xτ : List (Move (F₁ ⊕ₛ F₂) G)) : Path .idle xτ (.wait g (Sum.inl q)) →
      FlatRel h σ τ b ((.run (Sum.inl q), .run q P, xσ), (.wait (Sum.inr g) (Sum.inl q), .idle, xτ))
        (.run (Sum.inr g), .idle, ((.run (Sum.inl q), .run q P, xσ), xτ))
  | chwait (b : Bool) (g : G.Op) (q : F₁.Op) (e : E.Op) (k : E.Ar e → Prog E (F₁.Ar q))
      (xσ : List (Move E F₂)) (xτ : List (Move (F₁ ⊕ₛ F₂) G)) :
      Path .idle xτ (.wait g (Sum.inl q)) →
      FlatRel h σ τ b ((.wait (Sum.inl q) e, .wait q e k, xσ),
          (.wait (Sum.inr g) (Sum.inl q), .idle, xτ))
        (.wait (Sum.inr g) e, .idle, ((.wait (Sum.inl q) e, .wait q e k, xσ), xτ))
  | csrun (b : Bool) (g : G.Op) (q : F₂.Op) (xσ : List (Move E F₂))
      (xτ : List (Move (F₁ ⊕ₛ F₂) G)) : Path .idle xτ (.wait g (Sum.inr q)) →
      FlatRel h σ τ b ((.run (Sum.inr q), .idle, xσ), (.wait (Sum.inr g) (Sum.inr q), .idle, xτ))
        (.run (Sum.inr g), .idle, ((.run (Sum.inr q), .idle, xσ), xτ))
  | cswait (b : Bool) (g : G.Op) (q : F₂.Op) (e : E.Op) (xσ : List (Move E F₂))
      (xτ : List (Move (F₁ ⊕ₛ F₂) G)) : Path .idle xτ (.wait g (Sum.inr q)) →
      FlatRel h σ τ b ((.wait (Sum.inr q) e, .idle, xσ), (.wait (Sum.inr g) (Sum.inr q), .idle, xτ))
        (.wait (Sum.inr g) e, .idle, ((.wait (Sum.inr q) e, .idle, xσ), xτ))

/-- The left-hand side is simulated by the right-hand side. -/
def flatSim (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    LTS.Simulation (flatL h σ τ) (flatR h σ τ) where
  R := FlatRel h σ τ true
  init := .idle true [] [] (.nil _)
  step := by
    intro z z' w l hr hs
    cases hr with
    | idle _ xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e hA => cases hA
      | right g' hB =>
        cases hB with
        | askL q hf =>
          cases hf
          exact ⟨_, .vis (LTS.PairStep.askL q (Reduction.Step.ask (R := h.toReduction) q))
            (.nil _), .fwd q xσ xτ hτ⟩
        | askR g hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          exact ⟨_, .vis (LTS.PairStep.askR g (LTS.CompStep.right _ hx)) (.nil _),
            .grun true g xσ _ hp⟩
      | sync f hA hB => cases hB
    | fwd q xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf with | tau hc => exact (hc : False).elim
        | tau₂ hx => cases hx
      | left e hA => cases hA
      | right g' hB => cases hB with
        | retL q r hf => cases hf with | ret hc => cases hc
      | sync f hA hB =>
        cases hB with
        | callL q m hf =>
          cases hf with
          | call hc =>
            cases hc
            cases hA with
            | askL q hh =>
              cases hh
              exact ⟨_, .nil _, .hrun true q (h q) xσ xτ hτ⟩
    | hrun _ q P xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh with | tau hc => exact (hc : False).elim
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e hA =>
        cases hA with
        | callL q m hh =>
          cases hh with
          | call hc =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.callL q m (Reduction.Step.call (R := h.toReduction) rfl))
              (.nil _), .hwait true q m _ xσ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB =>
        cases hA with
        | retL q r hh =>
          cases hh with
          | ret hc =>
            cases hc
            cases hB with
            | replyL _ _ _ hf =>
              cases hf
              exact ⟨_, .nil _, .back q _ xσ xτ hτ⟩
    | hwait _ q e k xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e' hA =>
        cases hA with
        | replyL q e n hh =>
          cases hh
          exact ⟨_, .vis (LTS.PairStep.replyL q e n
            (Reduction.Step.resume (R := h.toReduction) q e k n)) (.nil _),
            .hrun true q (k n) xσ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB => cases hA
    | back q r xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf with | tau hc => exact (hc : False).elim
        | tau₂ hx => cases hx
      | left e hA => cases hA
      | right g' hB =>
        cases hB with
        | retL q r' hf =>
          cases hf with
          | ret hc =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.retL q _ (Reduction.Step.ret (R := h.toReduction) rfl))
              (.nil _), .idle true xσ xτ hτ⟩
      | sync f hA hB => cases hB with
        | callL q m hf => cases hf with | call hc => cases hc
    | grun _ g xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e hA => cases hA
      | right g' hB =>
        cases hB with
        | retR g r hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          exact ⟨_, .vis (LTS.PairStep.retR g r (LTS.CompStep.right _ hx)) (.nil _),
            .idle true xσ _ hp⟩
      | sync f hA hB =>
        cases hB with
        | callR g m hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          cases hA with
          | askL q hh =>
            cases hh
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _
              (LTS.PairStep.askL q (Reduction.Step.ask (R := h.toReduction) q)) hx)) (.nil _),
              .chrun true g q (h q) xσ _ hp⟩
          | askR q hσ =>
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ (LTS.PairStep.askR q hσ) hx))
              (.nil _), .csrun true g q _ _ hp⟩
    | chrun _ g q P xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh with | tau hc => exact (hc : False).elim
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e hA =>
        cases hA with
        | callL q m hh =>
          cases hh with
          | call hc =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.callR g m (LTS.CompStep.left _ (LTS.PairStep.callL q m
              (Reduction.Step.call (R := h.toReduction) rfl)))) (.nil _),
              .chwait true g q m _ xσ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB =>
        cases hA with
        | retL q r hh =>
          cases hh with
          | ret hc =>
            cases hc
            cases hB with
            | replyR g _ _ hx =>
              obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
              cases hst
              exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ (LTS.PairStep.retL q _
                (Reduction.Step.ret (R := h.toReduction) rfl)) hx)) (.nil _),
                .grun true g xσ _ hp⟩
    | chwait _ g q e k xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e' hA =>
        cases hA with
        | replyL q e n hh =>
          cases hh
          exact ⟨_, .vis (LTS.PairStep.replyR g e n (LTS.CompStep.left _ (LTS.PairStep.replyL q e n
            (Reduction.Step.resume (R := h.toReduction) q e k n)))) (.nil _),
            .chrun true g q (k n) xσ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB => cases hA
    | csrun _ g q xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e hA =>
        cases hA with
        | callR q m hσ =>
          exact ⟨_, .vis (LTS.PairStep.callR g m (LTS.CompStep.left _ (LTS.PairStep.callR q m hσ)))
            (.nil _), .cswait true g q m _ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB =>
        cases hA with
        | retR q r hσ =>
          cases hB with
          | replyR g _ _ hx =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
            cases hst
            exact ⟨_, .tau (LTS.PairStep.tau₂ (LTS.CompStep.sync _ (LTS.PairStep.retR q r hσ) hx))
              (.nil _), .grun true g _ _ hp⟩
    | cswait _ g q e xσ xτ hτ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ hh => cases hh
        | tau₂ hx => cases hx
      | tau₂ hB => cases hB with
        | tau₁ hf => cases hf
        | tau₂ hx => cases hx
      | left e' hA =>
        cases hA with
        | replyR q e n hσ =>
          exact ⟨_, .vis (LTS.PairStep.replyR g e n (LTS.CompStep.left _
            (LTS.PairStep.replyR q e n hσ))) (.nil _), .csrun true g q _ xτ hτ⟩
      | right g' hB => cases hB
      | sync f hA hB => cases hA

/-- The right-hand side is simulated by the left-hand side. -/
def flatSim' (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    LTS.Simulation (flatR h σ τ) (flatL h σ τ) where
  R w z := FlatRel h σ τ false z w
  init := .idle false [] [] (.nil _)
  step := by
    intro w w' z l hr hs
    cases hr with
    | idle _ xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx => obtain ⟨_, hst, -⟩ := tstep_path hx hτ; cases hst
      | askL q hh =>
        cases hh
        exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askL q
            (Reduction.Step.ask (R := (fstH F₁ F₂).toReduction) q)))
          (.tau (LTS.CompStep.sync _ (LTS.PairStep.askL q (Reduction.Step.ask (R := h.toReduction) q))
            (LTS.PairStep.callL (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) q (Sum.inl q) (Reduction.Step.call (R := (fstH F₁ F₂).toReduction)
              rfl))) (.nil _)), .hrun false q (h q) xσ xτ hτ⟩
      | askR g hI =>
        cases hI with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askR g hx)) (.nil _),
            .grun false g xσ _ hp⟩
    | hrun _ q P xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh with | tau hc => exact (hc : False).elim
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx => obtain ⟨_, hst, -⟩ := tstep_path hx hτ; cases hst
      | callL q m hh =>
        cases hh with
        | call hc =>
          cases hc
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callL q m
            (Reduction.Step.call (R := h.toReduction) rfl))) (.nil _), .hwait false q m _ xσ xτ hτ⟩
      | retL q r hh =>
        cases hh with
        | ret hc =>
          cases hc
          exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retL q _
              (Reduction.Step.ret (R := h.toReduction) rfl))
            (LTS.PairStep.replyL (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) q (Sum.inl q) _ (Reduction.Step.resume
              (R := (fstH F₁ F₂).toReduction) q (Sum.inl q) (fun n => .pure n) _)))
            (.vis (LTS.CompStep.right _ (LTS.PairStep.retL q _
              (Reduction.Step.ret (R := (fstH F₁ F₂).toReduction) rfl))) (.nil _)),
            .idle false xσ xτ hτ⟩
    | hwait _ q e k xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx => obtain ⟨_, hst, -⟩ := tstep_path hx hτ; cases hst
      | replyL q e n hh =>
        cases hh
        exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyL q e n
          (Reduction.Step.resume (R := h.toReduction) q e k n))) (.nil _),
          .hrun false q (k n) xσ xτ hτ⟩
    | grun _ g xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          cases hA with
          | askL q hh =>
            cases hh
            exact ⟨_, .tau (LTS.CompStep.sync _
              (LTS.PairStep.askL q (Reduction.Step.ask (R := h.toReduction) q))
              (LTS.PairStep.callR (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) g (Sum.inl q) hx)) (.nil _), .chrun false g q (h q) xσ _ hp⟩
          | askR q hσ =>
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.askR q hσ)
              (LTS.PairStep.callR (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) g (Sum.inr q) hx)) (.nil _), .csrun false g q _ _ hp⟩
      | callR g m hI => cases hI with | left _ hA => cases hA
      | retR g r hI =>
        cases hI with
        | right _ hx =>
          obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
          cases hst
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.retR g r hx)) (.nil _),
            .idle false xσ _ hp⟩
    | chrun _ g q P xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh with | tau hc => exact (hc : False).elim
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx =>
          cases hA with
          | retL q r hh =>
            cases hh with
            | ret hc =>
              cases hc
              obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
              cases hst
              exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retL q _
                (Reduction.Step.ret (R := h.toReduction) rfl))
                (LTS.PairStep.replyR (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) g (Sum.inl q) _ hx)) (.nil _), .grun false g xσ _ hp⟩
      | callR g m hI =>
        cases hI with
        | left _ hA =>
          cases hA with
          | callL q m hh =>
            cases hh with
            | call hc =>
              cases hc
              exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callL q m
                (Reduction.Step.call (R := h.toReduction) rfl))) (.nil _),
                .chwait false g q m _ xσ xτ hτ⟩
      | retR g r hI =>
        cases hI with
        | right _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hτ; cases hst
    | chwait _ g q e k xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx => cases hA
      | replyR g e n hI =>
        cases hI with
        | left _ hA =>
          cases hA with
          | replyL q e n hh =>
            cases hh
            exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyL q e n
              (Reduction.Step.resume (R := h.toReduction) q e k n))) (.nil _),
              .chrun false g q (k n) xσ xτ hτ⟩
    | csrun _ g q xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx =>
          cases hA with
          | retR q r hσ =>
            obtain ⟨_, hst, hp⟩ := tstep_path hx hτ
            cases hst
            exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retR q r hσ)
              (LTS.PairStep.replyR (L₁ := (fstH F₁ F₂).toReduction.toLTS) (L₂ := τ.toLTS) g (Sum.inr q) r hx)) (.nil _), .grun false g _ _ hp⟩
      | callR g m hI =>
        cases hI with
        | left _ hA =>
          cases hA with
          | callR q m hσ =>
            exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callR q m hσ)) (.nil _),
              .cswait false g q m _ xτ hτ⟩
      | retR g r hI =>
        cases hI with
        | right _ hx => obtain ⟨_, hst, -⟩ := tstep_path hx hτ; cases hst
    | cswait _ g q e xσ xτ hτ =>
      cases hs with
      | tau₁ hh => cases hh
      | tau₂ hI =>
        cases hI with
        | tau₁ hA => cases hA with
          | tau₁ hh => cases hh
          | tau₂ hx => cases hx
        | tau₂ hx => cases hx
        | sync f hA hx => cases hA
      | replyR g e n hI =>
        cases hI with
        | left _ hA =>
          cases hA with
          | replyR q e n hσ =>
            exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyR q e n hσ)) (.nil _),
              .csrun false g q _ xτ hτ⟩

theorem pair_comp_pair_fst (h : Handler E F₁) (σ : Strategy E F₂) (τ : Strategy (F₁ ⊕ₛ F₂) G) :
    ((Strategy.ofHandler h).pair σ).comp
        ((Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).pair τ) =
      (Strategy.ofHandler h).pair (((Strategy.ofHandler h).pair σ).comp τ) :=
  LTS.Denotes.eq_of_simulation
    ((denotes_pair (Handler.denotes_toLTS h) σ.denotes_toLTS).comp
      (denotes_pair (Handler.denotes_toLTS _) τ.denotes_toLTS))
    (denotes_pair (Handler.denotes_toLTS h)
      ((denotes_pair (Handler.denotes_toLTS h) σ.denotes_toLTS).comp τ.denotes_toLTS))
    (flatSim h σ τ) (flatSim' h σ τ)

end Silmaril.Proofs.Games.Pair
