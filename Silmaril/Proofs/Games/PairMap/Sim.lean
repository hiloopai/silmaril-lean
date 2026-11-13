module

public import Silmaril.Games.Pair.Thms
public import Silmaril.Proofs.Games.PairMap.Lift

/-!
# Pairing is functorial in its left factor: proofs

For `σ₁ : Strategy E F₁`, `σ₂ : Strategy E F₂` and `τ : Strategy F₁ G`,

`(σ₁ ∥ σ₂) ≫ ((inl ≫ τ) ∥ inr) = (σ₁ ≫ τ) ∥ σ₂`,

where `inl ≫ τ` is `τ` over the lower interface `F₁ ⊕ₛ F₂` (`τL`) and `inr` forwards `F₂` to
the right summand (`πR`). On the left, a `G`-round of `τ` calls `σ₁` through the left half of
the pairing; an `F₂`-round is forwarded to `σ₂` by `πR`. On the right, `τ` runs on `σ₁` and `σ₂`
runs beside it. The two transition systems (`mapL`, `mapR`) simulate each other with the same
plays of `σ₁`, `τ` and `σ₂` (`MapRel`, `MapRel'`); the forwarding of `πR` may hold a question
(`MapRel.fwd`) or an answer (`MapRel.back`) for one step, which the reverse simulation avoids
by forwarding eagerly. No hypothesis on the strategies is needed: the state of `σ₂` is only
reached through `πR`, and that of `σ₁` only through `τ`.
-/

public section

namespace Silmaril.Proofs.Games.PairMap

open Silmaril.Games

universe u

variable {E F₁ F₂ G : Sig.{u}}

/-- `τ` over the lower interface `F₁ ⊕ₛ F₂`. -/
abbrev τL (F₂ : Sig.{u}) (τ : Strategy F₁ G) : Strategy (F₁ ⊕ₛ F₂) G :=
  (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inl F₁ F₂))).comp τ

/-- Forwarding `F₂` to the right summand. -/
abbrev πR (F₁ F₂ : Sig.{u}) : Handler (F₁ ⊕ₛ F₂) F₂ := Handler.ofHom (Sig.Hom.inr F₁ F₂)

/-- The transition system of `(σ₁ ∥ σ₂) ≫ ((inl ≫ τ) ∥ inr)`. -/
abbrev mapL (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) : LTS E (G ⊕ₛ F₂) :=
  (σ₁.toLTS.pair σ₂.toLTS).comp ((τL F₂ τ).toLTS.pair (πR F₁ F₂).toReduction.toLTS)

/-- The transition system of `(σ₁ ≫ τ) ∥ σ₂`. -/
abbrev mapR (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) : LTS E (G ⊕ₛ F₂) :=
  (σ₁.toLTS.comp τ.toLTS).pair σ₂.toLTS

theorem lift_snoc {y' : List (Move (F₁ ⊕ₛ F₂) G)} {y : List (Move F₁ G)}
    (hy : y' = y.map (liftMove F₂)) (o : Move F₁ G) :
    y' ++ [liftMove F₂ o] = (y ++ [o]).map (liftMove F₂) := by
  rw [hy, List.map_append]
  rfl

theorem of_mem_snoc' {τ : Strategy F₁ G} {y' : List (Move (F₁ ⊕ₛ F₂) G)} {y : List (Move F₁ G)}
    (hy : y' = y.map (liftMove F₂)) {o' : Move (F₁ ⊕ₛ F₂) G} (h : y' ++ [o'] ∈ τL F₂ τ) :
    ∃ o, o' = liftMove F₂ o ∧ y ++ [o] ∈ τ := by
  rw [hy] at h
  exact of_mem_snoc h

theorem mem_snoc_lift {τ : Strategy F₁ G} {y' : List (Move (F₁ ⊕ₛ F₂) G)} {y : List (Move F₁ G)}
    (hy : y' = y.map (liftMove F₂)) {o : Move F₁ G} (h : y ++ [o] ∈ τ) :
    y' ++ [liftMove F₂ o] ∈ τL F₂ τ := by
  rw [lift_snoc hy]
  exact mem_map_lift h

/-- Corresponding states, from `mapL` to `mapR`. -/
inductive MapRel (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    (mapL σ₁ σ₂ τ).State → (mapR σ₁ σ₂ τ).State → Prop
  | idle (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) (y' : List (Move (F₁ ⊕ₛ F₂) G))
      (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) → x₂ ∈ σ₂ → Path .idle x₂ .idle →
      MapRel σ₁ σ₂ τ ((.idle, x₁, x₂), (.idle, y', .idle)) (.idle, (x₁, y), x₂)
  | grun (g : G.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      x₂ ∈ σ₂ → Path .idle x₂ .idle →
      MapRel σ₁ σ₂ τ ((.idle, x₁, x₂), (.run (.inl g), y', .idle)) (.run (.inl g), (x₁, y), x₂)
  | gcall (g : G.Op) (f : F₁.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      x₂ ∈ σ₂ → Path .idle x₂ .idle →
      MapRel σ₁ σ₂ τ ((.run (.inl f), x₁, x₂), (.wait (.inl g) (.inl f), y', .idle))
        (.run (.inl g), (x₁, y), x₂)
  | gwait (g : G.Op) (f : F₁.Op) (m : E.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      x₂ ∈ σ₂ → Path .idle x₂ .idle →
      MapRel σ₁ σ₂ τ ((.wait (.inl f) m, x₁, x₂), (.wait (.inl g) (.inl f), y', .idle))
        (.wait (.inl g) m, (x₁, y), x₂)
  | fwd (q : F₂.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      x₂ ++ [.inr (.ask q)] ∈ σ₂ → Path .idle x₂ .idle →
      MapRel σ₁ σ₂ τ ((.idle, x₁, x₂), (.run (.inr q), y', .run q (πR F₁ F₂ q)))
        (.run (.inr q), (x₁, y), x₂ ++ [.inr (.ask q)])
  | srun (q : F₂.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₂ (.run q) →
      MapRel σ₁ σ₂ τ ((.run (.inr q), x₁, x₂),
          (.wait (.inr q) (.inr q), y', .wait q (.inr q) fun n => .pure n))
        (.run (.inr q), (x₁, y), x₂)
  | swait (q : F₂.Op) (m : E.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₂ (.wait q m) →
      MapRel σ₁ σ₂ τ ((.wait (.inr q) m, x₁, x₂),
          (.wait (.inr q) (.inr q), y', .wait q (.inr q) fun n => .pure n))
        (.wait (.inr q) m, (x₁, y), x₂)
  | back (q : F₂.Op) (r : F₂.Ar q) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      x₂ ++ [.inr (.ans q r)] ∈ σ₂ → Path .idle x₂ (.run q) →
      MapRel σ₁ σ₂ τ ((.idle, x₁, x₂ ++ [.inr (.ans q r)]), (.run (.inr q), y', .run q (.pure r)))
        (.run (.inr q), (x₁, y), x₂)

/-- `mapL` is simulated by `mapR`. -/
def mapSim (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    LTS.Simulation (mapL σ₁ σ₂ τ) (mapR σ₁ σ₂ τ) where
  R := MapRel σ₁ σ₂ τ
  init := .idle [] [] [] [] rfl σ₂.nil_mem (.nil _)
  step := by
    intro z z' w l hr hs
    cases hr with
    | idle x₁ x₂ y' y hy hx₂ hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA => cases hA
      | right g hB =>
        cases hB with
        | askL g hx =>
          cases hx with
          | mk _ hm =>
            obtain ⟨o, ho, hτ⟩ := of_mem_snoc' hy hm
            obtain rfl := liftMove_eq_inr ho
            exact ⟨_, .vis (LTS.PairStep.askL g (LTS.CompStep.right _ (Strategy.TStep.mk y _ hτ)))
              (.nil _), .grun g x₁ x₂ _ _ (lift_snoc hy (.inr (.ask g))) hx₂ hp₂⟩
        | askR q hπ =>
          cases hπ
          have hm := σ₂.receptive hx₂ hp₂ (Step.ask (E := E) (F := F₂) q) trivial
          exact ⟨_, .vis (LTS.PairStep.askR q (Strategy.TStep.mk x₂ _ hm)) (.nil _),
            .fwd q x₁ x₂ y' y hy hm hp₂⟩
      | sync f hA hB => cases hB
    | grun g x₁ x₂ y' y hy hx₂ hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA => cases hA
      | right g' hB =>
        cases hB with
        | retL g r hx =>
          cases hx with
          | mk _ hm =>
            obtain ⟨o, ho, hτ⟩ := of_mem_snoc' hy hm
            obtain rfl := liftMove_eq_inr ho
            exact ⟨_, .vis (LTS.PairStep.retL g r (LTS.CompStep.right _ (Strategy.TStep.mk y _ hτ)))
              (.nil _), .idle x₁ x₂ _ _ (lift_snoc hy (.inr (.ans g r))) hx₂ hp₂⟩
      | sync f hA hB =>
        cases hB with
        | callL g m hx =>
          cases hx with
          | mk _ hm =>
            obtain ⟨o, ho, hτ⟩ := of_mem_snoc' hy hm
            cases hA with
            | askL f hx₁ =>
              cases hx₁ with
              | mk _ hm₁ =>
                obtain rfl := liftMove_eq_askL ho
                exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _ (Strategy.TStep.mk x₁ _ hm₁)
                  (Strategy.TStep.mk y _ hτ))) (.nil _),
                  .gcall g f _ x₂ _ _ (lift_snoc hy (.inl (.ask f))) hx₂ hp₂⟩
            | askR q _ => exact (liftMove_ne_askR ho).elim
    | gcall g f x₁ x₂ y' y hy hx₂ hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA =>
        cases hA with
        | callL f m hx₁ =>
          cases hx₁ with
          | mk _ hm₁ =>
            exact ⟨_, .vis (LTS.PairStep.callL g m (LTS.CompStep.left _
              (Strategy.TStep.mk x₁ _ hm₁))) (.nil _), .gwait g f m _ x₂ y' y hy hx₂ hp₂⟩
      | right g' hB => cases hB
      | sync f' hA hB =>
        cases hB with
        | replyL g m n hx =>
          cases hx with
          | mk _ hm =>
            obtain ⟨o, ho, hτ⟩ := of_mem_snoc' hy hm
            cases hA with
            | retL f r hx₁ =>
              cases hx₁ with
              | mk _ hm₁ =>
                obtain rfl := liftMove_eq_ansL ho
                exact ⟨_, .tau (LTS.PairStep.tau₁ (LTS.CompStep.sync _ (Strategy.TStep.mk x₁ _ hm₁)
                  (Strategy.TStep.mk y _ hτ))) (.nil _),
                  .grun g _ x₂ _ _ (lift_snoc hy (.inl (.ans f _))) hx₂ hp₂⟩
    | gwait g f m x₁ x₂ y' y hy hx₂ hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA =>
        cases hA with
        | replyL f m n hx₁ =>
          cases hx₁ with
          | mk _ hm₁ =>
            exact ⟨_, .vis (LTS.PairStep.replyL g m n (LTS.CompStep.left _
              (Strategy.TStep.mk x₁ _ hm₁))) (.nil _), .gcall g f _ x₂ y' y hy hx₂ hp₂⟩
      | right g' hB => cases hB
      | sync f' hA hB => cases hA
    | fwd q x₁ x₂ y' y hy hm hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h with | tau hc => exact (hc : False).elim
      | left e hA => cases hA
      | right g hB =>
        cases hB with
        | retR q r hπ => cases hπ with | ret hc => cases hc
      | sync f hA hB =>
        cases hB with
        | callR q m hπ =>
          cases hπ with
          | call hc =>
            cases hc
            cases hA with
            | askR q hx₂ =>
              cases hx₂ with
              | mk _ _ =>
                exact ⟨_, .nil _, .srun q x₁ _ y' y hy (hp₂.append (.single (.ask q)))⟩
    | srun q x₁ x₂ y' y hy hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA =>
        cases hA with
        | callR q m hx =>
          cases hx with
          | mk _ hm =>
            exact ⟨_, .vis (LTS.PairStep.callR q m (Strategy.TStep.mk x₂ _ hm)) (.nil _),
              .swait q m x₁ _ y' y hy (hp₂.append (.single (.call q m)))⟩
      | right g hB => cases hB
      | sync f hA hB =>
        cases hB with
        | replyR q m n hπ =>
          cases hπ
          cases hA with
          | retR q r hx =>
            cases hx with
            | mk _ hm => exact ⟨_, .nil _, .back q _ x₁ x₂ y' y hy hm hp₂⟩
    | swait q m x₁ x₂ y' y hy hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | left e hA =>
        cases hA with
        | replyR q m n hx =>
          cases hx with
          | mk _ hm =>
            exact ⟨_, .vis (LTS.PairStep.replyR q m n (Strategy.TStep.mk x₂ _ hm)) (.nil _),
              .srun q x₁ _ y' y hy (hp₂.append (.single (.reply q m n)))⟩
      | right g hB => cases hB
      | sync f hA hB => cases hA
    | back q r x₁ x₂ y' y hy hm hp₂ =>
      cases hs with
      | tau₁ hA => cases hA with
        | tau₁ h => cases h
        | tau₂ h => cases h
      | tau₂ hB => cases hB with
        | tau₁ h => cases h
        | tau₂ h => cases h with | tau hc => exact (hc : False).elim
      | left e hA => cases hA
      | right g hB =>
        cases hB with
        | retR q r' hπ =>
          cases hπ with
          | ret hc =>
            cases hc
            exact ⟨_, .vis (LTS.PairStep.retR q r (Strategy.TStep.mk x₂ _ hm)) (.nil _),
              .idle x₁ _ y' y hy hm (hp₂.append (.single (.ret q r)))⟩
      | sync f hA hB =>
        cases hB with
        | callR q m hπ => cases hπ with | call hc => cases hc

/-- Corresponding states, from `mapR` to `mapL` (forwarding eagerly). -/
inductive MapRel' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    (mapR σ₁ σ₂ τ).State → (mapL σ₁ σ₂ τ).State → Prop
  | idle (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂)) (y' : List (Move (F₁ ⊕ₛ F₂) G))
      (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) → Path .idle x₁ .idle →
      Path .idle y .idle →
      MapRel' σ₁ σ₂ τ (.idle, (x₁, y), x₂) ((.idle, x₁, x₂), (.idle, y', .idle))
  | grun (g : G.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₁ .idle → Path .idle y (.run g) →
      MapRel' σ₁ σ₂ τ (.run (.inl g), (x₁, y), x₂) ((.idle, x₁, x₂), (.run (.inl g), y', .idle))
  | gcall (g : G.Op) (f : F₁.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₁ (.run f) → Path .idle y (.wait g f) →
      MapRel' σ₁ σ₂ τ (.run (.inl g), (x₁, y), x₂)
        ((.run (.inl f), x₁, x₂), (.wait (.inl g) (.inl f), y', .idle))
  | gwait (g : G.Op) (f : F₁.Op) (m : E.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₁ (.wait f m) → Path .idle y (.wait g f) →
      MapRel' σ₁ σ₂ τ (.wait (.inl g) m, (x₁, y), x₂)
        ((.wait (.inl f) m, x₁, x₂), (.wait (.inl g) (.inl f), y', .idle))
  | srun (q : F₂.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₁ .idle → Path .idle y .idle →
      MapRel' σ₁ σ₂ τ (.run (.inr q), (x₁, y), x₂)
        ((.run (.inr q), x₁, x₂), (.wait (.inr q) (.inr q), y', .wait q (.inr q) fun n => .pure n))
  | swait (q : F₂.Op) (m : E.Op) (x₁ : List (Move E F₁)) (x₂ : List (Move E F₂))
      (y' : List (Move (F₁ ⊕ₛ F₂) G)) (y : List (Move F₁ G)) : y' = y.map (liftMove F₂) →
      Path .idle x₁ .idle → Path .idle y .idle →
      MapRel' σ₁ σ₂ τ (.wait (.inr q) m, (x₁, y), x₂)
        ((.wait (.inr q) m, x₁, x₂), (.wait (.inr q) (.inr q), y', .wait q (.inr q) fun n => .pure n))

/-- `mapR` is simulated by `mapL`. -/
def mapSim' (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    LTS.Simulation (mapR σ₁ σ₂ τ) (mapL σ₁ σ₂ τ) where
  R := MapRel' σ₁ σ₂ τ
  init := .idle [] [] [] [] rfl (.nil _) (.nil _)
  step := by
    intro z z' w l hr hs
    cases hr with
    | idle x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            obtain ⟨_, hst⟩ := step_of_snoc hmτ hpy
            cases hst
      | tau₂ h => cases h
      | askL g h =>
        cases h with
        | right _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askL g
              (Strategy.TStep.mk y' _ (mem_snoc_lift hy hmτ)))) (.nil _),
              .grun g x₁ x₂ _ _ (lift_snoc hy (.inr (.ask g))) hp₁
                (hpy.append (.single (.ask g)))⟩
      | askR q h =>
        cases h with
        | mk _ hm₂ =>
          exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.askR q (Reduction.Step.ask q)))
            (.tau (LTS.CompStep.sync _ (LTS.PairStep.askR q (Strategy.TStep.mk x₂ _ hm₂))
              (LTS.PairStep.callR (L₁ := (τL F₂ τ).toLTS) (L₂ := (πR F₁ F₂).toReduction.toLTS) q (Sum.inr q)
                (Reduction.Step.call rfl))) (.nil _)),
            .srun q x₁ _ y' y hy hp₁ hpy⟩
    | grun g x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f h₁ hτ =>
          cases h₁ with
          | mk _ hm₁ =>
            cases hτ with
            | mk _ hmτ =>
              obtain ⟨_, hst⟩ := step_of_snoc hm₁ hp₁
              cases hst with
              | ask f =>
                exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.askL f
                  (Strategy.TStep.mk x₁ _ hm₁)) (LTS.PairStep.callL (L₁ := (τL F₂ τ).toLTS) (L₂ := (πR F₁ F₂).toReduction.toLTS) g (Sum.inl f)
                    (Strategy.TStep.mk y' _ (mem_snoc_lift hy hmτ)))) (.nil _),
                  .gcall g f _ x₂ _ _ (lift_snoc hy (.inl (.ask f)))
                    (hp₁.append (.single (.ask f))) (hpy.append (.single (.call g f)))⟩
      | tau₂ h => cases h
      | callL g m h =>
        cases h with
        | left _ h₁ =>
          cases h₁ with
          | mk _ hm₁ =>
            obtain ⟨_, hst⟩ := step_of_snoc hm₁ hp₁
            cases hst
      | retL g r h =>
        cases h with
        | right _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            exact ⟨_, .vis (LTS.CompStep.right _ (LTS.PairStep.retL g r
              (Strategy.TStep.mk y' _ (mem_snoc_lift hy hmτ)))) (.nil _),
              .idle x₁ x₂ _ _ (lift_snoc hy (.inr (.ans g r))) hp₁
                (hpy.append (.single (.ret g r)))⟩
    | gcall g f x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f' h₁ hτ =>
          cases h₁ with
          | mk _ hm₁ =>
            cases hτ with
            | mk _ hmτ =>
              obtain ⟨_, hst⟩ := step_of_snoc hmτ hpy
              cases hst with
              | reply _ _ r =>
                exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retL f r
                  (Strategy.TStep.mk x₁ _ hm₁)) (LTS.PairStep.replyL (L₁ := (τL F₂ τ).toLTS) (L₂ := (πR F₁ F₂).toReduction.toLTS) g (Sum.inl f) r
                    (Strategy.TStep.mk y' _ (mem_snoc_lift hy hmτ)))) (.nil _),
                  .grun g _ x₂ _ _ (lift_snoc hy (.inl (.ans f r)))
                    (hp₁.append (.single (.ret f r))) (hpy.append (.single (.reply g f r)))⟩
      | tau₂ h => cases h
      | callL g m h =>
        cases h with
        | left _ h₁ =>
          cases h₁ with
          | mk _ hm₁ =>
            exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callL f m
              (Strategy.TStep.mk x₁ _ hm₁))) (.nil _),
              .gwait g f m _ x₂ y' y hy (hp₁.append (.single (.call f m))) hpy⟩
      | retL g r h =>
        cases h with
        | right _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            obtain ⟨_, hst⟩ := step_of_snoc hmτ hpy
            cases hst
    | gwait g f m x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f' h₁ _ =>
          cases h₁ with
          | mk _ hm₁ =>
            obtain ⟨_, hst⟩ := step_of_snoc hm₁ hp₁
            cases hst
      | tau₂ h => cases h
      | replyL g m n h =>
        cases h with
        | left _ h₁ =>
          cases h₁ with
          | mk _ hm₁ =>
            exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyL f m n
              (Strategy.TStep.mk x₁ _ hm₁))) (.nil _),
              .gcall g f _ x₂ y' y hy (hp₁.append (.single (.reply f m n))) hpy⟩
    | srun q x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            obtain ⟨_, hst⟩ := step_of_snoc hmτ hpy
            cases hst
      | tau₂ h => cases h
      | callR q m h =>
        cases h with
        | mk _ hm₂ =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.callR q m
            (Strategy.TStep.mk x₂ _ hm₂))) (.nil _), .swait q m x₁ _ y' y hy hp₁ hpy⟩
      | retR q r h =>
        cases h with
        | mk _ hm₂ =>
          exact ⟨_, .tau (LTS.CompStep.sync _ (LTS.PairStep.retR q r (Strategy.TStep.mk x₂ _ hm₂))
              (LTS.PairStep.replyR (L₁ := (τL F₂ τ).toLTS) (L₂ := (πR F₁ F₂).toReduction.toLTS) q (Sum.inr q) r (Reduction.Step.resume
                (R := (πR F₁ F₂).toReduction) q (Sum.inr q) (fun n => .pure n) r)))
            (.vis (LTS.CompStep.right _ (LTS.PairStep.retR q r (Reduction.Step.ret rfl)))
              (.nil _)),
            .idle x₁ _ y' y hy hp₁ hpy⟩
    | swait q m x₁ x₂ y' y hy hp₁ hpy =>
      cases hs with
      | tau₁ h =>
        cases h with
        | tau₁ h => cases h
        | tau₂ h => cases h
        | sync f _ hτ =>
          cases hτ with
          | mk _ hmτ =>
            obtain ⟨_, hst⟩ := step_of_snoc hmτ hpy
            cases hst
      | tau₂ h => cases h
      | replyR q m n h =>
        cases h with
        | mk _ hm₂ =>
          exact ⟨_, .vis (LTS.CompStep.left _ (LTS.PairStep.replyR q m n
            (Strategy.TStep.mk x₂ _ hm₂))) (.nil _), .srun q x₁ _ y' y hy hp₁ hpy⟩

/-- **Pairing is functorial in its left factor.** -/
theorem pair_comp_mapLeft (σ₁ : Strategy E F₁) (σ₂ : Strategy E F₂) (τ : Strategy F₁ G) :
    (σ₁.pair σ₂).comp ((τL F₂ τ).pair (Strategy.ofHandler (πR F₁ F₂))) = (σ₁.comp τ).pair σ₂ :=
  LTS.Denotes.eq_of_simulation
    ((LTS.Denotes.pair σ₁.denotes_toLTS σ₂.denotes_toLTS).comp
      (LTS.Denotes.pair (τL F₂ τ).denotes_toLTS (Handler.denotes_toLTS _)))
    ((LTS.Denotes.comp σ₁.denotes_toLTS τ.denotes_toLTS).pair σ₂.denotes_toLTS)
    (mapSim σ₁ σ₂ τ) (mapSim' σ₁ σ₂ τ)

end Silmaril.Proofs.Games.PairMap
