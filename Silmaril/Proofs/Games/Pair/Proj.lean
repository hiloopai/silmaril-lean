module

public import Silmaril.Games.Handler.Thms
public import Silmaril.Proofs.Games.Pair.LTS

/-!
# Restricting a pairing to its left interface: proofs

`(σ₁.pair σ₂).restrict (Sig.Hom.inl F₁ F₂) = σ₁`. The composite of the
pairing with the forwarding handler of the left injection and the transition
system of `σ₁` simulate each other. The forwarding handler may hold a
question it has received but not yet forwarded (`ProjRel.asked`), or an
answer of `σ₁` it has not yet returned (`ProjRel.ret`); receptiveness of `σ₁`
covers the first case.
-/

public section

namespace Silmaril.Proofs.Games.Pair

open Silmaril.Games

universe u

variable {E F₁ F₂ : Sig.{u}}

/-- The forwarding handler of the left injection. -/
abbrev fstH (F₁ F₂ : Sig.{u}) : Handler (F₁ ⊕ₛ F₂) F₁ := Handler.ofHom (Sig.Hom.inl F₁ F₂)

/-- The transition system of the restricted pairing. -/
abbrev projL (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) : LTS E F₁ :=
  (σ₁.toLTS.pair σ₂.toLTS).comp (fstH F₁ F₂).toReduction.toLTS

/-- Simulation relation, from the restricted pairing to `σ₁`. -/
inductive ProjRel (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (projL σ₁ σ₂).State → σ₁.toLTS.State → Prop
  | idle (x : List (Move E F₁)) : x ∈ σ₁ → Path .idle x .idle →
      ProjRel σ₁ σ₂ ((.idle, x, []), .idle) x
  | asked (x : List (Move E F₁)) (q : F₁.Op) : x ∈ σ₁ → Path .idle x .idle →
      x ++ [.inr (.ask q)] ∈ σ₁ →
      ProjRel σ₁ σ₂ ((.idle, x, []), .run q (fstH F₁ F₂ q)) (x ++ [.inr (.ask q)])
  | run (x : List (Move E F₁)) (q : F₁.Op) : Path .idle x (.run q) →
      ProjRel σ₁ σ₂ ((.run (Sum.inl q), x, []), .wait q (Sum.inl q) fun n => .pure n) x
  | wait (x : List (Move E F₁)) (q : F₁.Op) (m : E.Op) : Path .idle x (.wait q m) →
      ProjRel σ₁ σ₂ ((.wait (Sum.inl q) m, x, []), .wait q (Sum.inl q) fun n => .pure n) x
  | ret (x : List (Move E F₁)) (q : F₁.Op) (r : F₁.Ar q) : Path .idle x (.run q) →
      x ++ [.inr (.ans q r)] ∈ σ₁ →
      ProjRel σ₁ σ₂ ((.idle, x ++ [.inr (.ans q r)], []), .run q (.pure r)) x

/-- The restricted pairing is simulated by `σ₁`. -/
def projSim (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    LTS.Simulation (projL σ₁ σ₂) σ₁.toLTS where
  R := ProjRel σ₁ σ₂
  init := .idle [] σ₁.nil_mem (.nil _)
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
          have hm := σ₁.receptive hx hp (.ask q) trivial
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
          | askL q hx' =>
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
        | callL q m hx' =>
          cases hx' with
          | mk _ hm =>
            exact ⟨_, .vis (Strategy.TStep.mk x _ hm) (.nil _),
              .wait _ q m (hp.append (.single (.call q m)))⟩
      | right g ht => cases ht
      | sync f hs ht =>
        cases ht with
        | resume _ _ _ r =>
          cases hs with
          | retL q r hx' =>
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
        | replyL q m n hx' =>
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

/-- Simulation relation, from `σ₁` to the restricted pairing. -/
inductive ProjRel' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    σ₁.toLTS.State → (projL σ₁ σ₂).State → Prop
  | idle (x : List (Move E F₁)) : Path .idle x .idle →
      ProjRel' σ₁ σ₂ x ((.idle, x, []), .idle)
  | run (x : List (Move E F₁)) (q : F₁.Op) : Path .idle x (.run q) →
      ProjRel' σ₁ σ₂ x ((.run (Sum.inl q), x, []), .wait q (Sum.inl q) fun n => .pure n)
  | wait (x : List (Move E F₁)) (q : F₁.Op) (m : E.Op) : Path .idle x (.wait q m) →
      ProjRel' σ₁ σ₂ x ((.wait (Sum.inl q) m, x, []), .wait q (Sum.inl q) fun n => .pure n)

/-- `σ₁` is simulated by the restricted pairing. -/
def projSim' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    LTS.Simulation σ₁.toLTS (projL σ₁ σ₂) where
  R := ProjRel' σ₁ σ₂
  init := .idle [] (.nil _)
  step := by
    intro x x' z l hr hs
    cases hs with
    | mk o hm =>
      obtain ⟨_, hl⟩ := σ₁.legal hm
      obtain ⟨y, hy, hst⟩ := Path.concat_iff.1 hl
      cases hr with
      | idle hp =>
        cases hy.det hp
        cases hst with
        | ask q =>
          exact ⟨_, .vis (LTS.CompStep.right _ (Reduction.Step.ask q))
            (.tau (LTS.CompStep.sync _ (LTS.PairStep.askL q (Strategy.TStep.mk x _ hm))
              (Reduction.Step.call rfl)) (.nil _)),
            .run _ q (hp.append (.single (.ask q)))⟩
      | run q hp =>
        cases hy.det hp
        cases hst with
        | call _ m =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callL q m (Strategy.TStep.mk x _ hm)))
            (.nil _), .wait _ q m (hp.append (.single (.call q m)))⟩
        | ret _ r =>
          exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retL q r (Strategy.TStep.mk x _ hm))
              (Reduction.Step.resume (R := (fstH F₁ F₂).toReduction) q (Sum.inl q)
                (fun n => .pure n) r))
            (.vis (LTS.CompStep.right _ (Reduction.Step.ret rfl)) (.nil _)),
            .idle _ (hp.append (.single (.ret q r)))⟩
      | wait q m hp =>
        cases hy.det hp
        cases hst with
        | reply _ _ n =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyL q m n
            (Strategy.TStep.mk x _ hm))) (.nil _), .run _ q (hp.append (.single (.reply q m n)))⟩

theorem pair_restrict_inl (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) :
    (σ₁.pair σ₂).restrict (Sig.Hom.inl F₁ F₂) = σ₁ :=
  LTS.Denotes.eq_of_simulation
    ((denotes_pair σ₁.denotes_toLTS σ₂.denotes_toLTS).comp (Handler.denotes_toLTS _))
    σ₁.denotes_toLTS (projSim σ₁ σ₂) (projSim' σ₁ σ₂)

end Silmaril.Proofs.Games.Pair
