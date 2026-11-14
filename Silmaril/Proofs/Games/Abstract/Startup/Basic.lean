module

public import Silmaril.Games.Abstract.Startup.Defs
public import Silmaril.Games.Abstract.Hiding.Thms
public import Mathlib.Data.List.Induction

/-!
# Startup: proofs

For startup-independent models, the startup part and the startup-erased
observation together determine the model.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.Startup

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Startup Silmaril.Games.Abstract.TraceModel

universe u

variable {S G : Game.{u}} {R : Type u}

theorem filterMap_runOf_of_start {a : List (PMove S G R)} (ha : ∀ x ∈ a, x.IsStart) :
    a.filterMap PMove.runOf = [] := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    obtain ⟨m, rfl⟩ := ha x (by simp)
    simpa [PMove.runOf] using ih fun y hy => ha y (by simp [hy])

theorem filterMap_runOf_eq_nil {q : List (PMove S G R)} (h : ∀ x ∈ q, ¬ x.IsRun) :
    q.filterMap PMove.runOf = [] := by
  induction q with
  | nil => rfl
  | cons x q ih =>
    have hx := h x (by simp)
    have hq := ih fun y hy => h y (by simp [hy])
    cases x with
    | run m => exact absurd ⟨m, rfl⟩ hx
    | _ => simpa [PMove.runOf] using hq

theorem eq_map_run {c : List (PMove S G R)} (hc : ∀ x ∈ c, x.IsRun) :
    c = (c.filterMap PMove.runOf).map .run := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    obtain ⟨m, rfl⟩ := hc x (by simp)
    simpa [PMove.runOf] using ih fun y hy => hc y (by simp [hy])

theorem filterMap_runOf_ready {a : List (PMove S G R)} (ha : ∀ x ∈ a, x.IsStart)
    (g : List G.Move) : (after a g).filterMap PMove.runOf = g := by
  rw [after, List.filterMap_append, filterMap_runOf_of_start ha]
  simp only [List.filterMap_cons, PMove.runOf, List.nil_append, List.filterMap_map]
  induction g <;> simp_all [Function.comp_def, PMove.runOf]

theorem not_isRun_of_start {x : PMove S G R} (h : x.IsStart) : ¬ x.IsRun := by
  obtain ⟨m, rfl⟩ := h
  rintro ⟨n, hn⟩
  cases hn

/-- A legal phased play has no run move, or is a successful startup followed by
run moves. -/
theorem legal_cases {p : List (PMove S G R)} (hp : p ∈ (Game.phased S G R).Legal) :
    (∀ x ∈ p, ¬ x.IsRun) ∨
      ∃ a g, (∀ x ∈ a, x.IsStart) ∧ p = after a g := by
  obtain ⟨⟨a, b, rfl, ha, hb⟩, -⟩ := hp
  rcases hb with rfl | ⟨r, rfl⟩ | ⟨c, rfl, hc⟩
  · left
    simpa using fun x hx => not_isRun_of_start (ha x hx)
  · left
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact not_isRun_of_start (ha x hx)
    · rw [List.mem_singleton.1 hx]
      rintro ⟨n, hn⟩
      cases hn
  · right
    exact ⟨a, c.filterMap PMove.runOf, ha, by rw [after, ← eq_map_run hc]⟩

/-- Extending a successful-startup play of `U` by Opponent run moves. -/
theorem extend {U : TraceModel (Game.phased S G R)} {a : List (PMove S G R)}
    {g₀ w : List G.Move} (h : after a g₀ ∈ U) (hw : ∀ o ∈ w, G.IsO o)
    (hl : after a (g₀ ++ w) ∈ (Game.phased S G R).Legal) :
    after a (g₀ ++ w) ∈ U := by
  induction w using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w o ih =>
    have key : after a (g₀ ++ (w ++ [o])) = after a (g₀ ++ w) ++ [PMove.run o] := by
      simp [after]
    rw [key] at hl ⊢
    have hl' : after a (g₀ ++ w) ∈ (Game.phased S G R).Legal :=
      (Game.phased S G R).legal_of_prefix hl (List.prefix_append _ _)
    exact U.closed.receptive (ih (fun o h => hw o (by simp [h])) hl') hl (hw o (by simp))

theorem prefix_ready {a : List (PMove S G R)} {g₀ g : List G.Move} (h : g₀ <+: g) :
    after a g₀ <+: after a g := by
  rw [after, after, List.prefix_append_right_inj, List.cons_prefix_cons]
  exact ⟨rfl, h.map _⟩

theorem prefix_after (a : List (PMove S G R)) (g : List G.Move) :
    a ++ [PMove.ready] <+: after a g := ⟨g.map PMove.run, by simp [after]⟩

theorem after_nil (a : List (PMove S G R)) : after a [] = a ++ [PMove.ready] := by simp [after]

theorem mem_of {T U : TraceModel (Game.phased S G R)} (hU : StartupIndep U)
    (hpre : startPart T = startPart U) (he : erased T = erased U) {p : List (PMove S G R)}
    (hp : p ∈ T) : p ∈ U := by
  rcases legal_cases (T.closed.legal hp) with hr | ⟨a, g, ha, rfl⟩
  · have : p ∈ startPart U := hpre ▸ ⟨hp, hr⟩
    exact this.1
  · have haT : a ++ [PMove.ready] ∈ startPart T := by
      refine ⟨T.closed.of_prefix hp (prefix_after a g), fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact not_isRun_of_start (ha x hx)
      · rw [List.mem_singleton.1 hx]; rintro ⟨n, hn⟩; cases hn
    have haU' := (hpre ▸ haT).1
    have haU : after a [] ∈ U := by rw [after_nil]; exact haU'
    have hg : g ∈ erased U := by
      rw [← he]
      have := filterMap_mem_hide (f := erase) hp
      rwa [show (after a g).filterMap erase.map = g from filterMap_runOf_ready ha g] at this
    obtain ⟨-, u, hu, g₀, w, rfl, hg₀, hw⟩ := hg
    have h₀ : after a g₀ ∈ U := by
      rcases hu with rfl | ⟨⟨q, hq, rfl⟩, -⟩
      · obtain rfl := List.prefix_nil.1 hg₀
        exact haU
      · rcases legal_cases (U.closed.legal hq) with hr | ⟨a', g', ha', rfl⟩
        · have : q.filterMap PMove.runOf = [] := filterMap_runOf_eq_nil hr
          change g₀ <+: q.filterMap PMove.runOf at hg₀
          rw [this] at hg₀
          obtain rfl := List.prefix_nil.1 hg₀
          exact haU
        · change g₀ <+: (after a' g').filterMap PMove.runOf at hg₀
          rw [filterMap_runOf_ready ha'] at hg₀
          have h₁ : after a' g₀ ∈ U := U.closed.of_prefix hq (prefix_ready hg₀)
          have h₂ : a' ++ [PMove.ready] ∈ U := U.closed.of_prefix hq (prefix_after a' g')
          exact (hU a' a g₀ ha' ha h₂ haU').1 h₁
    exact extend h₀ hw (T.closed.legal hp)

theorem eq_iff {T U : TraceModel (Game.phased S G R)} (hT : StartupIndep T)
    (hU : StartupIndep U) :
    T = U ↔ startPart T = startPart U ∧ erased T = erased U := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hpre, he⟩ => ?_⟩
  ext p
  exact ⟨mem_of hU hpre he, mem_of hT hpre.symm he.symm⟩

end Silmaril.Proofs.Games.Abstract.Startup
