module

public import Silmaril.Games.LTS.Defs

/-!
# Transition systems: proofs

Proofs for `Silmaril.Games.LTS.Thms`: runs compose, weak forward simulations
transport runs, and a simulation of reduction semantics induces a simulation
of their transition systems.
-/

public section

namespace Silmaril.Proofs.Games.LTS

open Silmaril.Games

universe u

variable {E F : Sig.{u}}

theorem run_append {L : LTS E F} {x y z : L.State} {s t : List (Move E F)}
    (h₁ : L.Run x s y) (h₂ : L.Run y t z) : L.Run x (s ++ t) z := by
  induction h₁ with
  | nil => exact h₂
  | tau h _ ih => exact .tau h (ih h₂)
  | vis h _ ih => exact .vis h (ih h₂)

theorem run_of_step {L : LTS E F} {x y : L.State} {l : Option (Move E F)}
    (h : L.step x l y) : L.Run x l.toList y := by
  cases l with
  | none => exact .tau h (.nil _)
  | some o => exact .vis h (.nil _)

theorem run_of_append {L : LTS E F} {x z : L.State} {s t : List (Move E F)}
    (h : L.Run x (s ++ t) z) : ∃ y, L.Run x s y ∧ L.Run y t z := by
  generalize hst : s ++ t = st at h
  induction h generalizing s with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hst
    exact ⟨_, .nil _, .nil _⟩
  | tau hs _ ih =>
    obtain ⟨y, h₁, h₂⟩ := ih hst
    exact ⟨y, .tau hs h₁, h₂⟩
  | vis hs hr ih =>
    cases s with
    | nil =>
      subst hst
      exact ⟨_, .nil _, .vis hs hr⟩
    | cons o s =>
      simp only [List.cons_append, List.cons.injEq] at hst
      obtain ⟨rfl, hst⟩ := hst
      obtain ⟨y, h₁, h₂⟩ := ih hst
      exact ⟨y, .vis hs h₁, h₂⟩

theorem run_cons_inv {L : LTS E F} {x z : L.State} {o : Move E F} {s : List (Move E F)}
    (h : L.Run x (o :: s) z) : ∃ x₁ x₂, L.Run x [] x₁ ∧ L.step x₁ (some o) x₂ ∧ L.Run x₂ s z := by
  generalize hl : o :: s = l at h
  induction h with
  | nil => cases hl
  | tau hs _ ih =>
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := ih hl
    exact ⟨x₁, x₂, .tau hs h₁, h₂, h₃⟩
  | vis hs hr _ =>
    cases hl
    exact ⟨_, _, .nil _, hs, hr⟩

theorem simulation_run {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) {x x' : L₁.State}
    {s : List (Move E F)} (h : L₁.Run x s x') :
    ∀ {y : L₂.State}, S.R x y → ∃ y', L₂.Run y s y' ∧ S.R x' y' := by
  induction h with
  | nil => intro y hy; exact ⟨y, .nil _, hy⟩
  | tau hs _ ih =>
    intro y hy
    obtain ⟨y₁, hr₁, hy₁⟩ := S.step hy hs
    obtain ⟨y', hr, hy'⟩ := ih hy₁
    exact ⟨y', run_append hr₁ hr, hy'⟩
  | vis hs _ ih =>
    intro y hy
    obtain ⟨y₁, hr₁, hy₁⟩ := S.step hy hs
    obtain ⟨y', hr, hy'⟩ := ih hy₁
    exact ⟨y', run_append hr₁ hr, hy'⟩

theorem simulation_traces {L₁ L₂ : LTS E F} (S : L₁.Simulation L₂) :
    L₁.Traces ⊆ L₂.Traces := fun _ ⟨_, h⟩ =>
  let ⟨y', hr, _⟩ := simulation_run S h S.init
  ⟨y', hr⟩

/-! ## Reduction semantics -/

theorem run_taus {R : Reduction E F} {q : F.Op} {d d' : R.Conf q}
    (h : Relation.ReflTransGen R.step d d') : R.toLTS.Run (.run q d) [] (.run q d') := by
  induction h with
  | refl => exact .nil _
  | tail _ hs ih => exact run_append ih (.tau (Reduction.Step.tau hs) (.nil _))

/-- The relation on states induced by a simulation of reduction semantics. -/
inductive SimRel {R₁ R₂ : Reduction E F} (S : R₁.Simulation R₂) : R₁.State → R₂.State → Prop
  | idle : SimRel S .idle .idle
  | run {q : F.Op} {c : R₁.Conf q} {d : R₂.Conf q} : S.rel c d → SimRel S (.run q c) (.run q d)
  | wait {q : F.Op} {m : E.Op} {k : E.Ar m → R₁.Conf q} {k' : E.Ar m → R₂.Conf q} :
      (∀ n, S.rel (k n) (k' n)) → SimRel S (.wait q m k) (.wait q m k')

/-- A simulation of reduction semantics is a simulation of their transition
systems. -/
def toLTSSimulation {R₁ R₂ : Reduction E F} (S : R₁.Simulation R₂) :
    LTS.Simulation R₁.toLTS R₂.toLTS where
  R := SimRel S
  init := .idle
  step := by
    intro x x' y l hr hs
    change Reduction.Step R₁ x l x' at hs
    cases hs with
    | ask q =>
      cases hr
      exact ⟨_, .vis (Reduction.Step.ask q) (.nil _), .run (S.start q)⟩
    | tau hc =>
      cases hr with
      | run hd =>
        obtain ⟨d', hstar, hd'⟩ := S.step hd hc
        exact ⟨_, run_taus hstar, .run hd'⟩
    | call hc =>
      cases hr with
      | run hd =>
        obtain ⟨d', hstar, k', hcall, hk⟩ := S.call hd hc
        exact ⟨_, run_append (run_taus hstar) (.vis (Reduction.Step.call hcall) (.nil _)),
          .wait hk⟩
    | resume q m k n =>
      cases hr with
      | wait hk => exact ⟨_, .vis (Reduction.Step.resume _ _ _ n) (.nil _), .run (hk n)⟩
    | ret hc =>
      cases hr with
      | run hd =>
        obtain ⟨d', hstar, hdone⟩ := S.done hd hc
        exact ⟨_, run_append (run_taus hstar) (.vis (Reduction.Step.ret hdone) (.nil _)), .idle⟩

end Silmaril.Proofs.Games.LTS
