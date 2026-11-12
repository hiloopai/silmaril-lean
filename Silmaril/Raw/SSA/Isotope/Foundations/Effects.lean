module

public import Silmaril.SSA.Isotope.Types.Thms
public import Mathlib.Order.Closure
public import Mathlib.Data.Bool.Basic

/-!
# Iteration of effects

Effects are upper bounds in a join-semilattice with bottom. Iteration is a
monotone closure operator; its fixed points admit arbitrarily many repetitions.
The choice of closure determines whether otherwise pure iteration records
possible divergence. It does not assert termination or semantic soundness of
primitive annotations.
-/

@[expose] public section

universe u

namespace Silmaril

/-- The effect of repeating a computation arbitrarily many times. -/
class EffectIteration (ε : Type u) [Preorder ε] where
  closure : ClosureOperator ε

variable {ε : Type u} [PartialOrder ε] [EffectIteration ε]

def iterEffect (e : ε) : ε := EffectIteration.closure e

def IsIterative (e : ε) : Prop := iterEffect e = e

theorem iterEffect_mono : Monotone (iterEffect : ε → ε) :=
  EffectIteration.closure.monotone

theorem le_iterEffect (e : ε) : e ≤ iterEffect e := EffectIteration.closure.le_closure e

@[simp] theorem iterEffect_idem (e : ε) : iterEffect (iterEffect e) = iterEffect e :=
  EffectIteration.closure.idempotent e

theorem isIterative_iterEffect (e : ε) : IsIterative (iterEffect e) := iterEffect_idem e

theorem IsIterative.iterEffect_le {e e' : ε} (he : IsIterative e') (h : e ≤ e') :
    iterEffect e ≤ e' := le_of_le_of_eq (iterEffect_mono h) he

theorem isIterative_iff_exists (e : ε) : IsIterative e ↔ ∃ e', iterEffect e' = e :=
  ⟨fun h => ⟨e, h⟩, by rintro ⟨e', rfl⟩; exact isIterative_iterEffect e'⟩

theorem isIterative_top [OrderTop ε] : IsIterative (⊤ : ε) :=
  le_antisymm le_top (le_iterEffect _)

/-- Fixpoints of a closure need not be upward closed. This is an additional
condition used by presentations that specify an upward-closed iterative subset. -/
def IterativeUpwardClosed : Prop :=
  ∀ {e e' : ε}, IsIterative e → e ≤ e' → IsIterative e'

/-- An upward-closed iterative predicate presents this closure only when the
closure is its least upper bound above each effect. -/
theorem isIterative_iff_of_least (P : ε → Prop)
    (closed : ∀ e, P (iterEffect e))
    (least : ∀ {e e'}, e ≤ e' → P e' → iterEffect e ≤ e') (e : ε) :
    IsIterative e ↔ P e := by
  constructor
  · intro h
    exact h ▸ closed e
  · intro h
    exact le_antisymm (least le_rfl h) (le_iterEffect e)

theorem iterativeUpwardClosed_of_least (P : ε → Prop)
    (upward : ∀ {e e'}, P e → e ≤ e' → P e')
    (closed : ∀ e, P (iterEffect e))
    (least : ∀ {e e'}, e ≤ e' → P e' → iterEffect e ≤ e') :
    IterativeUpwardClosed (ε := ε) := by
  intro e e' he hle
  exact (isIterative_iff_of_least P closed least e').mpr
    (upward ((isIterative_iff_of_least P closed least e).mp he) hle)

namespace EffectIteration

/-- A complete effect signature: iteration adds no effect. -/
@[instance_reducible] def complete (ε : Type u) [Preorder ε] : EffectIteration ε :=
  ⟨ClosureOperator.id ε⟩

/-- A conservative signature in which every loop has top effect.
On Booleans this records possible nontermination as the non-bottom effect. -/
@[instance_reducible] def partiality (ε : Type u) [PartialOrder ε] [OrderTop ε] : EffectIteration ε where
  closure := {
    toFun := fun _ => ⊤
    monotone' := fun _ _ _ => le_rfl
    le_closure' := fun _ => le_top
    idempotent' := fun _ => rfl
  }

end EffectIteration

end Silmaril
