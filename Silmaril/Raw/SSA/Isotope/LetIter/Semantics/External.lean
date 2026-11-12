module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Operational

/-!
# Let-iter divergence with externally divergent primitives

`prim f a s` states that an atomic instruction may perform an internally infinite
computation at this input and state. This is supplied by the instruction model;
a missing finite transition alone does not establish it. The existing finite
`Eval` and `Loop` relations are unchanged.

The extra divergence rule evaluates an instruction's argument finitely before
entering its divergent primitive computation. The original contextual and loop
rules are reused, with their continuation predicate left open.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics.External

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}

/-- One unfolding either follows the original contextual rules or enters an
externally diverging primitive after a finite argument evaluation. -/
inductive DivergenceStep (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (prim : Φ → Value α → σ → Prop)
    (continues : Config α ν Φ σ → Prop) : Config α ν Φ σ → Prop where
  | core {c} (h : Semantics.DivergenceStep instr free continues c) :
      DivergenceStep instr free prim continues c
  | primitive {n : Nat} {bound : BoundEnv α n} {f : Φ} {a : Tm ν Φ n}
      {s s' : σ} {value : Value α}
      (arg : Eval instr free bound a s value s') (diverges : prim f value s') :
      DivergenceStep instr free prim continues (.term bound (.op f a) s)

variable {instr : Φ → Value α → σ → Value α → σ → Prop} {free : FreeEnv ν α}
    {prim : Φ → Value α → σ → Prop}

theorem DivergenceStep.mono {R S : Config α ν Φ σ → Prop} {c : Config α ν Φ σ}
    (h : DivergenceStep instr free prim R c) (hRS : ∀ c, R c → S c) :
    DivergenceStep instr free prim S c := by
  cases h with
  | core h => exact .core (h.mono hRS)
  | primitive arg div => exact .primitive arg div

def Diverges (instr : Φ → Value α → σ → Value α → σ → Prop)
    (free : FreeEnv ν α) (prim : Φ → Value α → σ → Prop) (c : Config α ν Φ σ) : Prop :=
  ∃ R : Config α ν Φ σ → Prop, R c ∧ ∀ c, R c → DivergenceStep instr free prim R c

namespace Diverges

theorem coinduct (R : Config α ν Φ σ → Prop)
    (closed : ∀ c, R c → DivergenceStep instr free prim R c) {c : Config α ν Φ σ}
    (hc : R c) : Diverges instr free prim c := ⟨R, hc, closed⟩

theorem unfold {c : Config α ν Φ σ} (h : Diverges instr free prim c) :
    DivergenceStep instr free prim (Diverges instr free prim) c := by
  obtain ⟨R, hc, closed⟩ := h
  exact (closed c hc).mono (fun _ hr => ⟨R, hr, closed⟩)

theorem fold {c : Config α ν Φ σ}
    (h : DivergenceStep instr free prim (Diverges instr free prim) c) :
    Diverges instr free prim c := by
  refine ⟨fun x => x = c ∨ Diverges instr free prim x, Or.inl rfl, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact h.mono (fun _ h => Or.inr h)
  · exact hx.unfold.mono (fun _ h => Or.inr h)

/-- Existing internal divergence remains valid for every external divergence model. -/
theorem of_internal {c : Config α ν Φ σ} (h : Semantics.Diverges instr free c) :
    Diverges instr free prim c := by
  obtain ⟨R, hc, closed⟩ := h
  exact ⟨R, hc, fun c h => .core (closed c h)⟩

/-- The false primitive predicate recovers precisely the original divergence relation. -/
theorem false_iff {c : Config α ν Φ σ} :
    Diverges instr free (fun _ _ _ => False) c ↔ Semantics.Diverges instr free c := by
  constructor
  · rintro ⟨R, hc, closed⟩
    refine ⟨R, hc, ?_⟩
    intro c h
    cases closed c h with
    | core h => exact h
    | primitive _ div => exact div.elim
  · exact of_internal

/-- Enlarging the possible externally divergent outcomes preserves divergence. -/
theorem mono {other : Φ → Value α → σ → Prop}
    (hprim : ∀ f a s, prim f a s → other f a s) {c : Config α ν Φ σ}
    (h : Diverges instr free prim c) : Diverges instr free other c := by
  obtain ⟨R, hc, closed⟩ := h
  refine ⟨R, hc, ?_⟩
  intro c h
  cases closed c h with
  | core h => exact .core h
  | primitive arg div => exact .primitive arg (hprim _ _ _ div)

/-- The argument runs before entering the externally divergent instruction. -/
theorem primitive {n : Nat} {bound : BoundEnv α n} {f : Φ} {a : Tm ν Φ n}
    {s s' : σ} {value : Value α} (arg : Eval instr free bound a s value s')
    (div : prim f value s') : Diverges instr free prim (.term bound (.op f a) s) :=
  fold (.primitive arg div)

end Diverges

/-- Finite outcomes and divergent outcomes of the same atomic invocation are disjoint.
This is an additional model property, not imposed on nondeterministic models. -/
def Disjoint (instr : Φ → Value α → σ → Value α → σ → Prop)
    (prim : Φ → Value α → σ → Prop) : Prop :=
  ∀ f a s b s', instr f a s b s' → ¬ prim f a s

theorem disjoint_false : Disjoint instr (fun _ _ _ => False) := fun _ _ _ _ _ _ h => h

end Silmaril.Isotope.LetIter.Semantics.External
