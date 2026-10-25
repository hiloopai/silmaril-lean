module

public import Mathlib.Logic.Relation
public import Mathlib.Order.WellFounded
public import Cslib.Foundations.Relation.Defs

/-! # Infinite paths of a relation

An infinite trace follows actual transitions. Its coinductive presentation is
equivalent to a productive post-fixed point and, classically, to failure of
accessibility for the reversed relation. None of these definitions identify
finite stuckness with divergence or require determinism.
-/

@[expose] public section

namespace Silmaril

variable {A B : Type*}

/-- An infinite sequence of actual transitions beginning at a specified state. -/
def InfiniteTrace (R : A → A → Prop) (a : A) : Prop :=
  ∃ trace : Nat → A, trace 0 = a ∧ ∀ n, R (trace n) (trace (n + 1))

theorem InfiniteTrace.unfold {R : A → A → Prop} {a : A} (h : InfiniteTrace R a) :
    ∃ b, R a b ∧ InfiniteTrace R b := by
  obtain ⟨trace, first, next⟩ := h
  exact ⟨trace 1, by simpa only [first] using next 0,
    (fun n => trace (n + 1)), rfl, (fun n => next (n + 1))⟩

theorem InfiniteTrace.fold {R : A → A → Prop} {a b : A} (step : R a b)
    (h : InfiniteTrace R b) : InfiniteTrace R a := by
  obtain ⟨trace, first, next⟩ := h
  refine ⟨fun n => match n with | 0 => a | n + 1 => trace n, rfl, ?_⟩
  intro n
  cases n with
  | zero => simpa only [first] using step
  | succ n => exact next n

/-- Extract an infinite path from a productive coinductive witness. -/
theorem InfiniteTrace.coinduct {R : A → A → Prop} (P : A → Prop)
    (closed : ∀ a, P a → ∃ b, R a b ∧ P b) {a : A} (initial : P a) : InfiniteTrace R a := by
  classical
  let next : {x // P x} → {x // P x} := fun x =>
    ⟨Classical.choose (closed x.1 x.2), (Classical.choose_spec (closed x.1 x.2)).2⟩
  let trace : Nat → {x // P x} := fun n => next^[n] ⟨a, initial⟩
  refine ⟨fun n => (trace n).1, rfl, ?_⟩
  intro n
  have step := (Classical.choose_spec (closed (trace n).1 (trace n).2)).1
  simpa only [trace, Function.iterate_succ_apply'] using step

theorem InfiniteTrace.of_steps {R : A → A → Prop} {a b : A}
    (path : Relation.ReflTransGen R a b) (h : InfiniteTrace R b) : InfiniteTrace R a := by
  induction path with
  | refl => exact h
  | tail _ step ih => exact ih (InfiniteTrace.fold step h)

/-- A forward simulation maps every transition of an infinite path. -/
theorem InfiniteTrace.map {R : A → A → Prop} {S : B → B → Prop}
    (f : A → B) (preserves : ∀ a b, R a b → S (f a) (f b)) {a : A}
    (h : InfiniteTrace R a) : InfiniteTrace S (f a) := by
  obtain ⟨trace, first, next⟩ := h
  exact ⟨fun n => f (trace n), congrArg f first, fun n => preserves _ _ (next n)⟩

/-- Reflect an infinite path along a map while retaining a source invariant.
Each target transition must have an actual source transition; injectivity,
determinism, and a global source progress assumption are unnecessary. -/
theorem InfiniteTrace.of_map {R : A → A → Prop} {S : B → B → Prop}
    (f : A → B) (P : A → Prop)
    (reflects : ∀ a b, P a → S (f a) b → ∃ next, R a next ∧ P next ∧ f next = b)
    {a : A} (valid : P a) (h : InfiniteTrace S (f a)) : InfiniteTrace R a := by
  apply InfiniteTrace.coinduct (fun a => P a ∧ InfiniteTrace S (f a)) ?_ ⟨valid, h⟩
  intro a state
  obtain ⟨b, step, tail⟩ := state.2.unfold
  obtain ⟨next, source, valid, mapped⟩ := reflects a b state.1 step
  exact ⟨next, source, valid, mapped ▸ tail⟩

/-- The greatest-fixed-point presentation and the actual path presentation agree. -/
theorem InfiniteTrace.iff_postfixed {R : A → A → Prop} {a : A} :
    InfiniteTrace R a ↔ ∃ P : A → Prop, P a ∧ ∀ a, P a → ∃ b, R a b ∧ P b := by
  constructor
  · intro h
    exact ⟨InfiniteTrace R, h, fun _ h => h.unfold⟩
  · rintro ⟨P, initial, closed⟩
    exact InfiniteTrace.coinduct P closed initial

/-- Mathlib's descending-chain characterization applies to the reversed
transition relation, i.e. to CSLib's strong normalization `Relation.SN`
(see `InfiniteTrace.iff_not_sn`). Accessibility quantifies over all successors
and includes stuck states; one terminating execution alone is not sufficient. -/
theorem InfiniteTrace.iff_not_acc {R : A → A → Prop} {a : A} :
    InfiniteTrace R a ↔ ¬ Acc (fun b a => R a b) a :=
  (not_acc_iff_exists_descending_chain (r := fun b a => R a b) (x := a)).symm

/-- A well-founded descent cannot support an infinite execution. -/
theorem InfiniteTrace.not_of_wellFounded {R : A → A → Prop}
    (h : WellFounded (fun b a => R a b)) (a : A) : ¬ InfiniteTrace R a :=
  fun trace => InfiniteTrace.iff_not_acc.mp trace (h.apply a)

/-- An infinite trace exists exactly when the state is not strongly normalizing
in CSLib's sense. -/
theorem InfiniteTrace.iff_not_sn {R : A → A → Prop} {a : A} :
    InfiniteTrace R a ↔ ¬ Relation.SN R a :=
  iff_not_acc

/-- A state has no infinite trace exactly when it is strongly normalizing in
CSLib's sense. -/
theorem InfiniteTrace.not_iff_sn {R : A → A → Prop} {a : A} :
    ¬ InfiniteTrace R a ↔ Relation.SN R a :=
  iff_not_sn.not_left

/-- A strongly normalizing state has no infinite trace. -/
theorem InfiniteTrace.not_of_sn {R : A → A → Prop} {a : A} (h : Relation.SN R a) :
    ¬ InfiniteTrace R a :=
  fun trace => iff_not_sn.mp trace h

/-- A terminating relation in CSLib's sense has no infinite trace. -/
theorem InfiniteTrace.not_of_terminating {R : A → A → Prop} (h : Relation.Terminating R)
    (a : A) : ¬ InfiniteTrace R a :=
  not_of_wellFounded h a

/-- A context's local execution either is infinite, or reaches a boundary in
finitely many local steps while the enclosing trace continues infinitely.
The one-step inversion premise is the only context-specific obligation. -/
theorem InfiniteTrace.context_decompose (R : A → A → Prop) (S : B → B → Prop)
    (plug : A → B) (boundary : A → B → Prop)
    (peel : ∀ a b, S (plug a) b →
      (∃ next, R a next ∧ b = plug next) ∨ boundary a b)
    {initial : A} (trace : InfiniteTrace S (plug initial)) :
    InfiniteTrace R initial ∨ ∃ a b,
      Relation.ReflTransGen R initial a ∧ boundary a b ∧ InfiniteTrace S b := by
  classical
  by_cases exited : ∃ a b, Relation.ReflTransGen R initial a ∧ boundary a b ∧ InfiniteTrace S b
  · exact Or.inr exited
  · left
    apply InfiniteTrace.coinduct (fun a => Relation.ReflTransGen R initial a ∧ InfiniteTrace S (plug a)) ?_
      ⟨.refl, trace⟩
    intro a state
    obtain ⟨b, step, tail⟩ := state.2.unfold
    rcases peel a b step with ⟨next, localStep, rfl⟩ | exit
    · exact ⟨next, localStep, state.1.tail localStep, tail⟩
    · exact False.elim (exited ⟨a, b, state.1, exit, tail⟩)

end Silmaril
