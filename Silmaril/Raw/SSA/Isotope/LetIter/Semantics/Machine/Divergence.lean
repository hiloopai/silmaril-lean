module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Machine.Agreement
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-!
# Infinite machine execution

Divergence is a greatest fixed point of actual single machine transitions.
The source divergence judgment, whose unfoldings can contain finite prefixes,
implies machine divergence. Missing primitive transitions are still stuck,
not divergent. The results here add no determinism premise to this implication.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.Machine

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

/-- A witness relation always supports another actual machine transition. -/
def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α)
    (c : Config α ν Φ σ) : Prop :=
  ∃ R : Config α ν Φ σ → Prop, R c ∧ ∀ c, R c → ∃ d, Step instr free c d ∧ R d

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}

namespace Diverges

/-- The coinductive machine judgment describes an actual infinite sequence of
single transitions, even when primitive operations are nondeterministic. -/
theorem iff_infiniteTrace {c : Config α ν Φ σ} :
    Diverges instr free c ↔ Silmaril.InfiniteTrace (Step instr free) c :=
  Silmaril.InfiniteTrace.iff_postfixed.symm

/-- Accessibility of the reversed transition relation excludes machine divergence. -/
theorem iff_not_acc {c : Config α ν Φ σ} :
    Diverges instr free c ↔ ¬ Acc (fun d c => Step instr free c d) c :=
  iff_infiniteTrace.trans Silmaril.InfiniteTrace.iff_not_acc

theorem unfold {c : Config α ν Φ σ} (h : Diverges instr free c) :
    ∃ d, Step instr free c d ∧ Diverges instr free d := by
  obtain ⟨R, hc, closed⟩ := h
  obtain ⟨d, step, hd⟩ := closed c hc
  exact ⟨d, step, R, hd, closed⟩

theorem fold {c d : Config α ν Φ σ} (h : Step instr free c d)
    (hd : Diverges instr free d) : Diverges instr free c := by
  refine ⟨fun x => x = c ∨ Diverges instr free x, Or.inl rfl, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨d, h, Or.inr hd⟩
  · obtain ⟨y, step, hy⟩ := hx.unfold
    exact ⟨y, step, Or.inr hy⟩

/-- A coinductive argument may take finitely many steps per unfolding, provided
it takes at least one step each time. This excludes unproductive witnesses. -/
theorem of_productive (R : Config α ν Φ σ → Prop)
    (closed : ∀ c, R c → ∃ first next,
      Step instr free c first ∧ Steps instr free first next ∧ R next)
    {c : Config α ν Φ σ} (hc : R c) : Diverges instr free c := by
  refine ⟨fun x => ∃ next, R next ∧ Steps instr free x next, ⟨c, hc, .refl _⟩, ?_⟩
  intro x hx
  obtain ⟨next, hn, path⟩ := hx
  cases path with
  | refl =>
      obtain ⟨first, next', step, tail, hn'⟩ := closed _ hn
      exact ⟨first, step, next', hn', tail⟩
  | cons step tail => exact ⟨_, step, next, hn, tail⟩

theorem not_stuck {c : Config α ν Φ σ} (h : Diverges instr free c) :
    ¬ (∀ d, ¬ Step instr free c d) := by
  obtain ⟨d, step, _⟩ := h.unfold
  exact fun stuck => stuck d step

end Diverges

theorem Steps.diverges {a b : Config α ν Φ σ} (h : Steps instr free a b)
    (hb : Diverges instr free b) : Diverges instr free a := by
  induction h with
  | refl => exact hb
  | cons step tail ih => exact Diverges.fold step (ih hb)

/-- Lift source divergence to evaluation or loop configurations with any continuation. -/
inductive SourceDiverges (instr : Φ → Value α → σ → Value α → σ → Prop) (free : FreeEnv ν α) :
    Config α ν Φ σ → Prop where
  | eval {n} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
      (h : Semantics.Diverges instr free (.term bound t s)) (k : Kont α ν Φ) :
      SourceDiverges instr free (.eval bound t k s)
  | loop {n} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)} {current : Value α} {s : σ}
      (h : Semantics.Diverges instr free (.loop bound body current s)) (k : Kont α ν Φ) :
      SourceDiverges instr free (.loop bound body current k s)

theorem SourceDiverges.productive {c : Config α ν Φ σ} (h : SourceDiverges instr free c) :
    ∃ first next, Step instr free c first ∧ Steps instr free first next ∧
      SourceDiverges instr free next := by
  cases h with
  | eval h k =>
      cases h.unfold with
      | op arg => exact ⟨_, _, .op .., .refl _, .eval arg _⟩
      | let₁_arg arg => exact ⟨_, _, .let₁ .., .refl _, .eval arg _⟩
      | let₁_body arg body =>
          exact ⟨_, _, .let₁ .., (eval_steps arg _).trans (Step.bind₁ ..).steps, .eval body _⟩
      | pair_left left => exact ⟨_, _, .pair .., .refl _, .eval left _⟩
      | pair_right left right =>
          exact ⟨_, _, .pair .., (eval_steps left _).trans (Step.pairLeft ..).steps, .eval right _⟩
      | let₂_arg arg => exact ⟨_, _, .let₂ .., .refl _, .eval arg _⟩
      | let₂_body arg body =>
          exact ⟨_, _, .let₂ .., (eval_steps arg _).trans (Step.bind₂ ..).steps, .eval body _⟩
      | inl arg => exact ⟨_, _, .inl .., .refl _, .eval arg _⟩
      | inr arg => exact ⟨_, _, .inr .., .refl _, .eval arg _⟩
      | case_scrutinee scrutinee => exact ⟨_, _, .case .., .refl _, .eval scrutinee _⟩
      | case_inl scrutinee branch =>
          exact ⟨_, _, .case ..,
            (eval_steps scrutinee _).trans (Step.caseLeft ..).steps, .eval branch _⟩
      | case_inr scrutinee branch =>
          exact ⟨_, _, .case ..,
            (eval_steps scrutinee _).trans (Step.caseRight ..).steps, .eval branch _⟩
      | abort arg => exact ⟨_, _, .abort .., .refl _, .eval arg _⟩
      | iter_init init => exact ⟨_, _, .iter .., .refl _, .eval init _⟩
      | iter_loop init loop =>
          exact ⟨_, _, .iter .., (eval_steps init _).trans (Step.initialized ..).steps, .loop loop _⟩
  | loop h k =>
      cases h.unfold with
      | loop_body body => exact ⟨_, _, .loop .., .refl _, .eval body _⟩
      | loop_step head tail =>
          exact ⟨_, _, .loop .., (eval_steps head _).trans (Step.continue ..).steps, .loop tail _⟩

/-- Source divergence produces genuinely infinite machine execution. -/
theorem source_diverges {n : Nat} {bound : BoundEnv α n} {t : Tm ν Φ n} {s : σ}
    (h : Semantics.Diverges instr free (.term bound t s)) (k : Kont α ν Φ) :
    Diverges instr free (.eval bound t k s) :=
  Diverges.of_productive (SourceDiverges instr free) (fun _ => SourceDiverges.productive) (.eval h k)

theorem source_loop_diverges {n : Nat} {bound : BoundEnv α n} {body : Tm ν Φ (n + 1)}
    {current : Value α} {s : σ}
    (h : Semantics.Diverges instr free (.loop bound body current s)) (k : Kont α ν Φ) :
    Diverges instr free (.loop bound body current k s) :=
  Diverges.of_productive (SourceDiverges instr free) (fun _ => SourceDiverges.productive) (.loop h k)

/-- The machine inherits determinism exactly when the primitive relation has it. -/
theorem Step.deterministic (hd : InstrDeterministic instr) {c a b : Config α ν Φ σ}
    (h : Step instr free c a) (g : Step instr free c b) : a = b := by
  cases h <;> cases g <;> try rfl
  rename_i f a b s s' k first b' s'' second
  obtain ⟨rfl, rfl⟩ := hd _ _ _ _ _ _ _ first second
  rfl

/-- Deterministic successful executions cannot also diverge. -/
theorem Steps.not_diverges (hd : InstrDeterministic instr) {c : Config α ν Φ σ}
    {value : Value α} {final : σ}
    (h : Steps instr free c (.ret value .halt final)) : ¬ Diverges instr free c := by
  generalize targetEq : Config.ret value Kont.halt final = target at h
  induction h with
  | refl =>
      intro d
      cases targetEq
      obtain ⟨_, step, _⟩ := d.unfold
      cases step
  | cons step tail ih =>
      intro d
      obtain ⟨_, other, hd'⟩ := d.unfold
      cases step.deterministic hd other
      exact ih targetEq hd'

/-- A missing primitive transition is stuck at the atomic instruction frame. -/
theorem primitive_stuck (f : Φ) (a : Value α) (k : Kont α ν Φ) (s : σ)
    (missing : ∀ b s', ¬ instr f a s b s') :
    (∀ d, ¬ Step instr free (.ret a (.op f k) s) d) ∧
      ¬ Diverges instr free (.ret a (.op f k) s) := by
  have stuck : ∀ d, ¬ Step instr free (.ret a (.op f k) s) d := by
    intro d step
    cases step with
    | apply _ h => exact missing _ _ h
  exact ⟨stuck, fun h => h.not_stuck stuck⟩

/-- Empty elimination cannot consume any runtime value, even one of the wrong shape. -/
theorem abort_stuck (v : Value α) (k : Kont α ν Φ) (s : σ) :
    (∀ d, ¬ Step instr free (.ret v (.abort k) s) d) ∧
      ¬ Diverges instr free (.ret v (.abort k) s) := by
  have stuck : ∀ d, ¬ Step instr free (.ret v (.abort k) s) d := by
    intro d step
    cases step
  exact ⟨stuck, fun h => h.not_stuck stuck⟩

end Silmaril.Isotope.LetIter.Semantics.Machine
