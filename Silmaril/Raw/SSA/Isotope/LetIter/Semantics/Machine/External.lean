module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Divergence

/-!
# Machine execution with externally divergent primitives

The finite transition relation is exactly `Machine.Step`. Divergence can either
keep taking those transitions or reach an atomic invocation declared divergent
by its model. Such an invocation is a terminal divergence observation, not an
invented self-loop and not a finite result. Setting its predicate to false
recovers the existing machine greatest fixed point.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine.External

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

/-- External divergence is observable only once the primitive input is ready. -/
def AtPrimitive (prim : Φ → Value α → σ → Prop) : Config α ν Φ σ → Prop
  | .ret a (.op f _) s => prim f a s
  | _ => False

/-- Infinite internal execution or a finite path to an externally divergent invocation. -/
def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (prim : Φ → Value α → σ → Prop) (c : Config α ν Φ σ) : Prop :=
  ∃ R : Config α ν Φ σ → Prop, R c ∧
    ∀ c, R c → (∃ d, Step instr free c d ∧ R d) ∨ AtPrimitive prim c

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {prim : Φ → Value α → σ → Prop}

namespace Diverges

theorem unfold {c : Config α ν Φ σ} (h : Diverges instr free prim c) :
    (∃ d, Step instr free c d ∧ Diverges instr free prim d) ∨ AtPrimitive prim c := by
  obtain ⟨R, hc, closed⟩ := h
  rcases closed c hc with ⟨d, step, hd⟩ | terminal
  · exact Or.inl ⟨d, step, R, hd, closed⟩
  · exact Or.inr terminal

theorem fold {c : Config α ν Φ σ}
    (h : (∃ d, Step instr free c d ∧ Diverges instr free prim d) ∨ AtPrimitive prim c) :
    Diverges instr free prim c := by
  refine ⟨fun x => x = c ∨ Diverges instr free prim x, Or.inl rfl, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · rcases h with ⟨d, step, hd⟩ | terminal
    · exact Or.inl ⟨d, step, Or.inr hd⟩
    · exact Or.inr terminal
  · rcases hx.unfold with ⟨d, step, hd⟩ | terminal
    · exact Or.inl ⟨d, step, Or.inr hd⟩
    · exact Or.inr terminal

theorem of_internal {c : Config α ν Φ σ} (h : Machine.Diverges instr free c) :
    Diverges instr free prim c := by
  obtain ⟨R, hc, closed⟩ := h
  exact ⟨R, hc, fun c h => Or.inl (closed c h)⟩

theorem false_iff {c : Config α ν Φ σ} :
    Diverges instr free (fun _ _ _ => False) c ↔ Machine.Diverges instr free c := by
  constructor
  · rintro ⟨R, hc, closed⟩
    refine ⟨R, hc, ?_⟩
    intro c h
    rcases closed c h with step | terminal
    · exact step
    · cases c with
      | eval => exact terminal.elim
      | loop => exact terminal.elim
      | ret value k s => cases k <;> exact terminal.elim
  · exact of_internal

theorem primitive (f : Φ) (a : Value α) (s : σ) (k : Kont α ν Φ) (h : prim f a s) :
    Diverges instr free prim (.ret a (.op f k) s) := fold (Or.inr h)

theorem of_steps {a b : Config α ν Φ σ} (path : Steps instr free a b)
    (hb : Diverges instr free prim b) : Diverges instr free prim a := by
  induction path with
  | refl => exact hb
  | cons step tail ih => exact fold (Or.inl ⟨_, step, ih hb⟩)

/-- A coinductive unfolding must take an actual step, or reach a justified
externally divergent invocation after finitely many actual steps. -/
theorem of_productive (R : Config α ν Φ σ → Prop)
    (closed : ∀ c, R c →
      (∃ first next, Step instr free c first ∧ Steps instr free first next ∧ R next) ∨
      (∃ terminal, Steps instr free c terminal ∧ AtPrimitive prim terminal))
    {c : Config α ν Φ σ} (hc : R c) : Diverges instr free prim c := by
  let S := fun x => ∃ next, Steps instr free x next ∧ (R next ∨ AtPrimitive prim next)
  refine ⟨S, ⟨c, .refl _, Or.inl hc⟩, ?_⟩
  intro x hx
  obtain ⟨next, path, hn⟩ := hx
  cases path with
  | cons step tail => exact Or.inl ⟨_, step, next, tail, hn⟩
  | refl =>
      rcases hn with hr | terminal
      · rcases closed _ hr with ⟨first, next, step, tail, hn⟩ | ⟨terminal, path, ht⟩
        · exact Or.inl ⟨first, step, next, tail, Or.inl hn⟩
        · cases path with
          | refl => exact Or.inr ht
          | cons step tail => exact Or.inl ⟨_, step, terminal, tail, Or.inr ht⟩
      · exact Or.inr terminal

end Diverges

/-- A finite transition cannot simultaneously enter external divergence in a disjoint model. -/
theorem step_not_atPrimitive (disjoint : Semantics.External.Disjoint instr prim)
    {a b : Config α ν Φ σ} (h : Step instr free a b) : ¬ AtPrimitive prim a := by
  cases h <;> try exact id
  exact disjoint _ _ _ _ _ ‹instr _ _ _ _ _›

/-- Successful deterministic runs exclude both internal and external divergence,
provided an atomic invocation cannot both return and diverge. -/
theorem steps_not_diverges (det : InstrDeterministic instr)
    (disjoint : Semantics.External.Disjoint instr prim) {c : Config α ν Φ σ}
    {value : Value α} {s : σ} (h : Steps instr free c (.ret value .halt s)) :
    ¬ Diverges instr free prim c := by
  generalize targetEq : Config.ret value Kont.halt s = target at h
  induction h with
  | refl =>
      intro div
      cases targetEq
      rcases div.unfold with ⟨_, step, _⟩ | terminal
      · cases step
      · exact terminal.elim
  | cons step tail ih =>
      intro div
      rcases div.unfold with ⟨_, other, hd⟩ | terminal
      · cases step.deterministic det other
        exact ih targetEq hd
      · exact step_not_atPrimitive disjoint step terminal

/-- Missing transitions alone do not count as external divergence. -/
theorem primitive_stuck (f : Φ) (a : Value α) (s : σ) (k : Kont α ν Φ)
    (missing : ∀ b s', ¬ instr f a s b s') (notExternal : ¬ prim f a s) :
    ¬ Diverges instr free prim (.ret a (.op f k) s) := by
  intro div
  rcases div.unfold with ⟨_, step, _⟩ | terminal
  · cases step with
    | apply _ finite => exact missing _ _ finite
  · exact notExternal terminal

end Silmaril.Isotope.LetIter.Semantics.Machine.External
