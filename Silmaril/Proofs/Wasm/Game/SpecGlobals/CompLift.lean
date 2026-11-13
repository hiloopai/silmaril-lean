module

public import Silmaril.Games.DivLTS.Thms

/-!
# Divergence-sensitive simulations under a fixed environment

`LTS.DivSimulation.compLeft L₁ S`: a divergence-sensitive simulation `S` of `L₂` by `L₂'`
lifts to one of the composite `L₁.comp L₂` by `L₁.comp L₂'` (the environment `L₁` fixed).
Silent steps of the upper system become silent composite steps, its moves on the shared
interface synchronise with the same move of `L₁`, and the measure is the one of `S` on the
upper component. Used for closed programs (`closedInstT`).

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Games

universe u

namespace CompLift

variable {E F G : Sig.{u}}

/-- Silent runs lift into a composite, the lower state fixed. -/
theorem silent_lift {L₁ : LTS E F} {L₂ : LTS F G} {x : L₁.State} {y z : L₂.State}
    (h : Relation.ReflTransGen L₂.Silent y z) :
    Relation.ReflTransGen (L₁.comp L₂).Silent (x, y) (x, z) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (LTS.CompStep.tau₂ hs)

theorem silent_lift_trans {L₁ : LTS E F} {L₂ : LTS F G} {x : L₁.State} {y z : L₂.State}
    (h : Relation.TransGen L₂.Silent y z) :
    Relation.TransGen (L₁.comp L₂).Silent (x, y) (x, z) := by
  induction h with
  | single hs => exact .single (LTS.CompStep.tau₂ hs)
  | tail _ hs ih => exact ih.tail (LTS.CompStep.tau₂ hs)

/-- A run with no moves is silent. -/
theorem run_nil {L : LTS E F} {y z : L.State} (h : L.Run y [] z) :
    Relation.ReflTransGen L.Silent y z := by
  generalize hl : ([] : List (Move E F)) = l at h
  induction h with
  | nil => exact .refl
  | tau hs _ ih => exact .head hs (ih hl)
  | vis _ _ _ => cases hl

/-- A run with one move: silent steps, the move, silent steps. -/
theorem run_one {L : LTS E F} {y z : L.State} {m : Move E F} (h : L.Run y [m] z) :
    ∃ y₁ y₂, Relation.ReflTransGen L.Silent y y₁ ∧ L.step y₁ (some m) y₂ ∧
      Relation.ReflTransGen L.Silent y₂ z := by
  generalize hl : [m] = l at h
  induction h with
  | nil => cases hl
  | tau hs _ ih =>
    obtain ⟨y₁, y₂, h₁, hm, h₂⟩ := ih hl
    exact ⟨y₁, y₂, .head hs h₁, hm, h₂⟩
  | vis hm r _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    exact ⟨_, _, .refl, hm, run_nil r⟩

theorem run_of_silent {L : LTS E F} {a b z : L.State} {t : List (Move E F)}
    (h : Relation.ReflTransGen L.Silent a b) (r : L.Run b t z) : L.Run a t z := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact r
  | head hs _ ih => exact .tau hs ih

theorem silent_run {L : LTS E F} {a b : L.State} (h : Relation.ReflTransGen L.Silent a b) :
    L.Run a [] b := run_of_silent h (.nil _)

/-- An upper move of the upper system, lifted. -/
theorem lift_right {L₁ : LTS E F} {L₂ : LTS F G} {x : L₁.State} {y z : L₂.State} {g : Ev G}
    (h : L₂.Run y [.inr g] z) : (L₁.comp L₂).Run (x, y) [.inr g] (x, z) := by
  obtain ⟨y₁, y₂, h₁, hm, h₂⟩ := run_one h
  exact run_of_silent (silent_lift h₁) (.vis (.right g hm) (silent_run (silent_lift (x := x) h₂)))

/-- A synchronisation, lifted: at least one silent composite step. -/
theorem lift_sync {L₁ : LTS E F} {L₂ : LTS F G} {x x' : L₁.State} {y z : L₂.State} {f : Ev F}
    (hx : L₁.step x (some (.inr f)) x') (h : L₂.Run y [.inl f] z) :
    Relation.TransGen (L₁.comp L₂).Silent (x, y) (x', z) := by
  obtain ⟨y₁, y₂, h₁, hm, h₂⟩ := run_one h
  have hs : (L₁.comp L₂).Silent (x, y₁) (x', y₂) := LTS.CompStep.sync f hx hm
  exact (Relation.TransGen.tail' (silent_lift h₁) hs).trans_left (silent_lift h₂)

variable {L₁ : LTS E F} {L₂ L₂' : LTS F G}

/-- The lifted relation. -/
def R' (S : L₂.DivSimulation L₂') (a : (L₁.comp L₂).State) (b : (L₁.comp L₂').State) : Prop :=
  a.1 = b.1 ∧ S.R a.2 b.2

/-- The lifted measure. -/
def Lt' (S : L₂.DivSimulation L₂') (a b : (L₁.comp L₂).State) : Prop := S.lt a.2 b.2

theorem lift_tau (S : L₂.DivSimulation L₂') {a a' : (L₁.comp L₂).State}
    {b : (L₁.comp L₂').State} (hR : R' S a b) (h : (L₁.comp L₂).step a none a') :
    (∃ b', Relation.TransGen (L₁.comp L₂').Silent b b' ∧ R' S a' b') ∨
      (R' S a' b ∧ Lt' S a' a) := by
  obtain ⟨x, y⟩ := a
  obtain ⟨x₂, y'⟩ := b
  obtain ⟨hx, hy⟩ := hR
  have hx' : x₂ = x := hx.symm
  subst hx'
  cases h with
  | tau₁ hs => exact .inl ⟨_, .single (LTS.CompStep.tau₁ hs), rfl, hy⟩
  | tau₂ hs =>
    rcases S.tau hy hs with ⟨z', hz, hR'⟩ | ⟨hR', hlt⟩
    · exact .inl ⟨_, silent_lift_trans hz, rfl, hR'⟩
    · exact .inr ⟨⟨rfl, hR'⟩, hlt⟩
  | sync f hx₁ hy₁ =>
    obtain ⟨z', hz, hR'⟩ := S.step hy hy₁
    exact .inl ⟨_, lift_sync hx₁ hz, rfl, hR'⟩

theorem lift_step (S : L₂.DivSimulation L₂') {a a' : (L₁.comp L₂).State}
    {b : (L₁.comp L₂').State} {l : Option (Move E G)} (hR : R' S a b)
    (h : (L₁.comp L₂).step a l a') :
    ∃ b', (L₁.comp L₂').Run b l.toList b' ∧ R' S a' b' := by
  cases l with
  | none =>
    rcases lift_tau S hR h with ⟨b', hb, hR'⟩ | ⟨hR', -⟩
    · exact ⟨b', silent_run hb.to_reflTransGen, hR'⟩
    · exact ⟨b, .nil _, hR'⟩
  | some m =>
    obtain ⟨x, y⟩ := a
    obtain ⟨x₂, y'⟩ := b
    obtain ⟨hx, hy⟩ := hR
    have hx' : x₂ = x := hx.symm
    subst hx'
    cases h with
    | left e hs => exact ⟨_, LTS.Run.of_step (LTS.CompStep.left e hs), rfl, hy⟩
    | right g hs =>
      obtain ⟨z', hz, hR'⟩ := S.step hy hs
      exact ⟨_, lift_right hz, rfl, hR'⟩

end CompLift

/-- **A divergence-sensitive simulation of the upper system lifts to its composite with a fixed
lower system.** -/
def DivSimulation.compLeft {E F G : Sig.{u}} (L₁ : LTS E F) {L₂ L₂' : LTS F G}
    (S : L₂.DivSimulation L₂') : (L₁.comp L₂).DivSimulation (L₁.comp L₂') where
  R := CompLift.R' S
  init := ⟨rfl, S.init⟩
  step hR h := CompLift.lift_step S hR h
  lt := CompLift.Lt' S
  wf := InvImage.wf (fun a : (L₁.comp L₂).State => a.2) S.wf
  tau hR h := CompLift.lift_tau S hR h

end Silmaril.Proofs.Wasm.Game.SpecGlobals
