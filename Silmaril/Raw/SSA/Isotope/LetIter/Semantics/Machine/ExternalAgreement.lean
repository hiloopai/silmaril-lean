module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.External

/-! # Source-to-machine agreement for externally divergent primitives -/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine.External

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {prim : Φ → Value α → σ → Prop}

/-- Enter a suspended source computation under a machine continuation. -/
def enter : Semantics.Config α ν Φ σ → Kont α ν Φ → Config α ν Φ σ
  | .term bound t s, k => .eval bound t k s
  | .loop bound body current s, k => .loop bound body current k s

/-- Each original divergence unfolding performs a nonempty finite machine prefix
and leaves precisely its indicated source continuation to run. -/
theorem core_progress {R : Semantics.Config α ν Φ σ → Prop} {c : Semantics.Config α ν Φ σ}
    (h : Semantics.DivergenceStep instr free R c) (k : Kont α ν Φ) :
    ∃ first next nextKont, Step instr free (enter c k) first ∧
      Steps instr free first (enter next nextKont) ∧ R next := by
  cases h with
  | op arg => exact ⟨_, _, _, .op .., .refl _, arg⟩
  | let₁_arg arg => exact ⟨_, _, _, .let₁ .., .refl _, arg⟩
  | let₁_body arg body =>
      exact ⟨_, _, _, .let₁ .., (eval_steps arg _).trans (Step.bind₁ ..).steps, body⟩
  | pair_left left => exact ⟨_, _, _, .pair .., .refl _, left⟩
  | pair_right left right =>
      exact ⟨_, _, _, .pair .., (eval_steps left _).trans (Step.pairLeft ..).steps, right⟩
  | let₂_arg arg => exact ⟨_, _, _, .let₂ .., .refl _, arg⟩
  | let₂_body arg body =>
      exact ⟨_, _, _, .let₂ .., (eval_steps arg _).trans (Step.bind₂ ..).steps, body⟩
  | inl arg => exact ⟨_, _, _, .inl .., .refl _, arg⟩
  | inr arg => exact ⟨_, _, _, .inr .., .refl _, arg⟩
  | case_scrutinee scrutinee => exact ⟨_, _, _, .case .., .refl _, scrutinee⟩
  | case_inl scrutinee branch =>
      exact ⟨_, _, _, .case .., (eval_steps scrutinee _).trans (Step.caseLeft ..).steps, branch⟩
  | case_inr scrutinee branch =>
      exact ⟨_, _, _, .case .., (eval_steps scrutinee _).trans (Step.caseRight ..).steps, branch⟩
  | abort arg => exact ⟨_, _, _, .abort .., .refl _, arg⟩
  | iter_init init => exact ⟨_, _, _, .iter .., .refl _, init⟩
  | iter_loop init loop =>
      exact ⟨_, _, _, .iter .., (eval_steps init _).trans (Step.initialized ..).steps, loop⟩
  | loop_body body => exact ⟨_, _, _, .loop .., .refl _, body⟩
  | loop_step head tail =>
      exact ⟨_, _, _, .loop .., (eval_steps head _).trans (Step.continue ..).steps, tail⟩

/-- Source divergence, including a justified internally divergent primitive,
is preserved by the machine under every surrounding continuation. -/
theorem source_diverges {c : Semantics.Config α ν Φ σ}
    (h : Semantics.External.Diverges instr free prim c) (k : Kont α ν Φ) :
    Diverges instr free prim (enter c k) := by
  let R := fun x => ∃ source k, x = enter source k ∧ Semantics.External.Diverges instr free prim source
  apply Diverges.of_productive R ?_ ⟨c, k, rfl, h⟩
  intro x hx
  obtain ⟨source, k, rfl, hd⟩ := hx
  cases hd.unfold with
  | core hc =>
      obtain ⟨first, next, nextKont, step, tail, hn⟩ := core_progress hc k
      exact Or.inl ⟨first, enter next nextKont, step, tail, next, nextKont, rfl, hn⟩
  | primitive arg div =>
      exact Or.inr ⟨_, .cons (.op ..) (eval_steps arg _), div⟩

/-- Convenient term-specialized statement of external divergence preservation. -/
theorem term_diverges {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.term bound t s)) (k : Kont α ν Φ) :
    Diverges instr free prim (.eval bound t k s) := source_diverges h k

/-- Convenient loop-specialized statement after the initializer has completed. -/
theorem loop_diverges {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current : Value α} {s : σ}
    (h : Semantics.External.Diverges instr free prim (.loop bound body current s)) (k : Kont α ν Φ) :
    Diverges instr free prim (.loop bound body current k s) := source_diverges h k

/-- Finite evaluation is still the original relation. It rules out extended
divergence under determinism and disjoint finite/divergent primitive outcomes. -/
theorem eval_not_diverges (det : InstrDeterministic instr)
    (disjoint : Semantics.External.Disjoint instr prim) {n : Nat} {bound : BoundEnv α n}
    {t : Tm ν Φ n} {s s' : σ} {value : Value α} (h : Eval instr free bound t s value s') :
    ¬ Semantics.External.Diverges instr free prim (.term bound t s) := by
  intro div
  exact steps_not_diverges det disjoint (eval_steps h .halt) (term_diverges div .halt)

theorem loop_not_diverges (det : InstrDeterministic instr)
    (disjoint : Semantics.External.Disjoint instr prim) {n : Nat} {bound : BoundEnv α n}
    {body : Tm ν Φ (n + 1)} {current value : Value α} {s s' : σ}
    (h : Loop instr free bound body current s value s') :
    ¬ Semantics.External.Diverges instr free prim (.loop bound body current s) := by
  intro div
  exact steps_not_diverges det disjoint (loop_steps h .halt) (loop_diverges div .halt)

end Silmaril.Isotope.LetIter.Semantics.Machine.External
