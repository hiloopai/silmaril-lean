module

public import Silmaril.Games.Pair.Thms
public import Silmaril.Games.Handler.Thms

/-!
# Restricting a pairing to its right interface

`(σ₁.pair σ₂).restrict (Sig.Hom.inr F₁ F₂) = σ₂`, the mirror image of `Silmaril.Games`'
`Strategy.pair_restrict_inl`. The proof mirrors `Silmaril.Proofs.Games.Pair.Proj` (two
simulations between the restricted pairing and `σ₂`), using only `Silmaril.Games` headers. It is a
candidate for `Silmaril.Games.Pair.Thms`.
-/

public section

namespace Silmaril.Wasm.Institution.Components.PairInr

open Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- The forwarding handler of the left injection. -/
abbrev sndH (F₁ F₂ : Sig.{u}) : Handler (F₁ ⊕ₛ F₂) F₂ := Handler.ofHom (Sig.Hom.inr F₁ F₂)

/-- The transition system of the restricted pairing. -/
abbrev projR (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) : LTS E F₂ :=
  (σ₁.toLTS.pair σ₂.toLTS).comp (sndH F₁ F₂).toReduction.toLTS

/-- Simulation relation, from the restricted pairing to `σ₂`. -/
inductive ProjRelR (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (projR σ₁ σ₂).State → σ₂.toLTS.State → Prop
  | idle (x : List (Move E F₂)) : x ∈ σ₂ → Path .idle x .idle →
      ProjRelR σ₁ σ₂ ((.idle, [], x), .idle) x
  | asked (x : List (Move E F₂)) (q : F₂.Op) : x ∈ σ₂ → Path .idle x .idle →
      x ++ [.inr (.ask q)] ∈ σ₂ →
      ProjRelR σ₁ σ₂ ((.idle, [], x), .run q (sndH F₁ F₂ q)) (x ++ [.inr (.ask q)])
  | run (x : List (Move E F₂)) (q : F₂.Op) : Path .idle x (.run q) →
      ProjRelR σ₁ σ₂ ((.run (Sum.inr q), [], x), .wait q (Sum.inr q) fun n => .pure n) x
  | wait (x : List (Move E F₂)) (q : F₂.Op) (m : E.Op) : Path .idle x (.wait q m) →
      ProjRelR σ₁ σ₂ ((.wait (Sum.inr q) m, [], x), .wait q (Sum.inr q) fun n => .pure n) x
  | ret (x : List (Move E F₂)) (q : F₂.Op) (r : F₂.Ar q) : Path .idle x (.run q) →
      x ++ [.inr (.ans q r)] ∈ σ₂ →
      ProjRelR σ₁ σ₂ ((.idle, [], x ++ [.inr (.ans q r)]), .run q (.pure r)) x

/-- The restricted pairing is simulated by `σ₂`. -/
def projSimR (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    LTS.Simulation (projR σ₁ σ₂) σ₂.toLTS where
  R := ProjRelR σ₁ σ₂
  init := .idle [] σ₂.nil_mem (.nil _)
  step := by
    intro z z' x l hr hs
    cases hr with
    | idle x hx hp =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs => cases hs
      | right g ht =>
        cases ht with
        | ask q =>
          have hm := σ₂.receptive hx hp (.ask q) trivial
          exact ⟨_, .vis (Strategy.TStep.mk x _ hm) (.nil _), .asked x q hx hp hm⟩
      | sync f hs ht => cases ht
    | asked x q hx hp hm =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
      | left e hs => cases hs
      | right g ht =>
        cases ht with
        | ret hc => cases hc
      | sync f hs ht =>
        cases ht with
        | call hc =>
          cases hc
          cases hs with
          | askR q hx' =>
            cases hx'
            exact ⟨_, .nil _, .run _ q (hp.append (.single (.ask q)))⟩
    | run x q hp =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | callR q m hx' =>
          cases hx' with
          | mk _ hm =>
            exact ⟨_, .vis (Strategy.TStep.mk x _ hm) (.nil _),
              .wait _ q m (hp.append (.single (.call q m)))⟩
      | right g ht => cases ht
      | sync f hs ht =>
        cases ht with
        | resume _ _ _ r =>
          cases hs with
          | retR q r hx' =>
            cases hx' with
            | mk _ hm => exact ⟨_, .nil _, .ret x q r hp hm⟩
    | wait x q m hp =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs
      | left e hs =>
        cases hs with
        | replyR q m n hx' =>
          cases hx' with
          | mk _ hm =>
            exact ⟨_, .vis (Strategy.TStep.mk x _ hm) (.nil _),
              .run _ q (hp.append (.single (.reply q m n)))⟩
      | right g ht => cases ht
      | sync f hs ht =>
        cases ht with
        | resume _ _ _ r => cases hs
    | ret x q r hp hm =>
      cases hs with
      | tau₁ hs => cases hs with
        | tau₁ hs => cases hs
        | tau₂ hs => cases hs
      | tau₂ hs => cases hs with | tau hc => exact (hc : False).elim
      | left e hs => cases hs
      | right g ht =>
        cases ht with
        | ret hc =>
          cases hc
          exact ⟨_, .vis (Strategy.TStep.mk x _ hm) (.nil _),
            .idle _ hm (hp.append (.single (.ret q r)))⟩
      | sync f hs ht =>
        cases ht with
        | call hc => cases hc

/-- Simulation relation, from `σ₂` to the restricted pairing. -/
inductive ProjRelR' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    σ₂.toLTS.State → (projR σ₁ σ₂).State → Prop
  | idle (x : List (Move E F₂)) : Path .idle x .idle →
      ProjRelR' σ₁ σ₂ x ((.idle, [], x), .idle)
  | run (x : List (Move E F₂)) (q : F₂.Op) : Path .idle x (.run q) →
      ProjRelR' σ₁ σ₂ x ((.run (Sum.inr q), [], x), .wait q (Sum.inr q) fun n => .pure n)
  | wait (x : List (Move E F₂)) (q : F₂.Op) (m : E.Op) : Path .idle x (.wait q m) →
      ProjRelR' σ₁ σ₂ x ((.wait (Sum.inr q) m, [], x), .wait q (Sum.inr q) fun n => .pure n)

/-- `σ₂` is simulated by the restricted pairing. -/
def projSimR' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    LTS.Simulation σ₂.toLTS (projR σ₁ σ₂) where
  R := ProjRelR' σ₁ σ₂
  init := .idle [] (.nil _)
  step := by
    intro x x' z l hr hs
    cases hs with
    | mk o hm =>
      obtain ⟨_, hl⟩ := σ₂.legal hm
      obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hl
      cases hr with
      | idle hp =>
        cases hy.det hp
        cases hst with
        | ask q =>
          exact ⟨_, .vis (LTS.CompStep.right _ (Reduction.Step.ask q))
            (.tau (LTS.CompStep.sync _ (LTS.PairStep.askR q (Strategy.TStep.mk x _ hm))
              (Reduction.Step.call rfl)) (.nil _)),
            .run _ q (hp.append (.single (.ask q)))⟩
      | run q hp =>
        cases hy.det hp
        cases hst with
        | call _ m =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callR q m (Strategy.TStep.mk x _ hm)))
            (.nil _), .wait _ q m (hp.append (.single (.call q m)))⟩
        | ret _ r =>
          exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retR q r (Strategy.TStep.mk x _ hm))
              (Reduction.Step.resume (R := (sndH F₁ F₂).toReduction) q (Sum.inr q)
                (fun n => .pure n) r))
            (.vis (LTS.CompStep.right _ (Reduction.Step.ret rfl)) (.nil _)),
            .idle _ (hp.append (.single (.ret q r)))⟩
      | wait q m hp =>
        cases hy.det hp
        cases hst with
        | reply _ _ n =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyR q m n
            (Strategy.TStep.mk x _ hm))) (.nil _), .run _ q (hp.append (.single (.reply q m n)))⟩

theorem pair_restrict_inr (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).restrict (Sig.Hom.inr F₁ F₂) = σ₂ :=
  LTS.Denotes.eq_of_simulation
    ((LTS.Denotes.pair σ₁.denotes_toLTS σ₂.denotes_toLTS).comp (Handler.denotes_toLTS _))
    σ₂.denotes_toLTS (projSimR σ₁ σ₂) (projSimR' σ₁ σ₂)

end Silmaril.Wasm.Institution.Components.PairInr
