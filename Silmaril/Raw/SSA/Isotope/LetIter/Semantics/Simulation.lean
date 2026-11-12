module

public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Fault.Structural
public import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.External.Structural

/-!
# Loop simulation along a relation between loop states

`Loop.map_body`, `LoopFault.map_body` and `External.Diverges.map_loop_body`
simulate one loop by another *at the same loop state*. The Elgot uniformity
law needs the general form, where the two loops carry different state spaces
related by a relation `R`: an exit of the simulated loop is an exit of the
simulating one, and a continuation step is matched by a continuation step whose
new states are again related.

The three lemmas below are the finite, faulting and infinite versions of that
one statement. They are deliberately stated in the direction that recovers a
`bound`/`body` loop from a `target`/`body'` loop, so that each use picks `R` to
point the way it needs.
-/

@[expose] public section

universe u v w q

namespace Silmaril.Isotope.LetIter.Semantics

open LocallyNameless

variable {α : Type u} {ν : Type v} {Φ : Type w} {σ : Type q}
    {instr : Φ → Value α → σ → Value α → σ → Prop}
    {faults : Φ → Value α → σ → σ → Prop}
    {prim : Φ → Value α → σ → Prop}
    {free : FreeEnv ν α}

/-- Induction along a finite iteration with the loop body and environment held
fixed, the counterpart of `LoopFault.induction_fixed`. -/
theorem Loop.induction_fixed {n : Nat} {bound : BoundEnv α n} {b : Tm ν Φ (n + 1)}
    {motive : Value α → σ → Value α → σ → Prop}
    (done : ∀ {current value : Value α} {s s' : σ},
      Eval instr free (extend bound current) b s (.inl value) s' → motive current s value s')
    (step : ∀ {current next value : Value α} {s mid s' : σ},
      Eval instr free (extend bound current) b s (.inr next) mid →
      Loop instr free bound b next mid value s' → motive next mid value s' →
      motive current s value s')
    {current value : Value α} {s s' : σ}
    (h : Loop instr free bound b current s value s') : motive current s value s' := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done h _ => exact done h
  | step h tail _ ih => exact step h tail (ih done step)
  | _ => trivial

/-- A finite iteration transfers along a relation between loop states that
reflects exits and matches continuation steps. -/
theorem Loop.simulate {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)} {R : Value α → Value α → Prop}
    (exit : ∀ {x y o : Value α} {s s' : σ}, R x y →
      Eval instr free (extend target y) body' s (.inl o) s' →
      Eval instr free (extend bound x) body s (.inl o) s')
    (cont : ∀ {x y y' : Value α} {s s' : σ}, R x y →
      Eval instr free (extend target y) body' s (.inr y') s' →
      ∃ x', R x' y' ∧ Eval instr free (extend bound x) body s (.inr x') s')
    {y value : Value α} {s s' : σ}
    (h : Loop instr free target body' y s value s') :
    ∀ {x : Value α}, R x y → Loop instr free bound body x s value s' := by
  induction h using Loop.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | done step _ => intro x hxy; exact .done (exit hxy step)
  | step head _ _ ih =>
      intro x hxy
      obtain ⟨x', hx', run⟩ := cont hxy head
      exact .step run (ih exit cont hx')
  | _ => trivial

/-- A faulting iteration transfers along a relation between loop states that
reflects faulting bodies and matches continuation steps. -/
theorem LoopFault.simulate {n m : Nat} {bound : BoundEnv α n} {target : BoundEnv α m}
    {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)} {R : Value α → Value α → Prop}
    (fault : ∀ {x y : Value α} {s s' : σ}, R x y →
      Fault instr faults free (extend target y) body' s s' →
      Fault instr faults free (extend bound x) body s s')
    (cont : ∀ {x y y' : Value α} {s s' : σ}, R x y →
      Eval instr free (extend target y) body' s (.inr y') s' →
      ∃ x', R x' y' ∧ Eval instr free (extend bound x) body s (.inr x') s')
    {y : Value α} {s s' : σ}
    (h : LoopFault instr faults free target body' y s s') :
    ∀ {x : Value α}, R x y → LoopFault instr faults free bound body x s s' := by
  induction h using LoopFault.rec (motive_1 := fun _ _ _ _ _ => True) with
  | body hf _ => intro x hxy; exact .body (fault hxy hf)
  | step head _ ih =>
      intro x hxy
      obtain ⟨x', hx', run⟩ := cont hxy head
      exact .step run (ih fault cont hx')
  | _ => trivial

/-- An infinite iteration transfers along a relation between loop states that
reflects divergent bodies and matches continuation steps. -/
theorem External.Diverges.simulate_loop {n m : Nat} {bound : BoundEnv α n}
    {target : BoundEnv α m} {body : Tm ν Φ (n + 1)} {body' : Tm ν Φ (m + 1)}
    {R : Value α → Value α → Prop}
    (divergent : ∀ {x y : Value α} {s : σ}, R x y →
      External.Diverges instr free prim (.term (extend target y) body' s) →
      External.Diverges instr free prim (.term (extend bound x) body s))
    (cont : ∀ {x y y' : Value α} {s s' : σ}, R x y →
      Eval instr free (extend target y) body' s (.inr y') s' →
      ∃ x', R x' y' ∧ Eval instr free (extend bound x) body s (.inr x') s')
    {x y : Value α} {s : σ} (hxy : R x y)
    (h : External.Diverges instr free prim (.loop target body' y s)) :
    External.Diverges instr free prim (.loop bound body x s) := by
  refine External.Diverges.coinduct
    (fun c => (∃ u w t, R u w ∧ c = .loop bound body u t ∧
        External.Diverges instr free prim (.loop target body' w t)) ∨
      External.Diverges instr free prim c) ?_ (Or.inl ⟨x, y, s, hxy, rfl, h⟩)
  rintro c (⟨u, w, t, huw, rfl, hd⟩ | hd)
  · cases hd.unfold with
    | core core => cases core with
      | loop_body step => exact .core (.loop_body (Or.inr (divergent huw step)))
      | loop_step head tail =>
          obtain ⟨u', hu', run⟩ := cont huw head
          exact .core (.loop_step run (Or.inl ⟨u', _, _, hu', rfl, tail⟩))
  · exact hd.unfold.mono (fun _ h => Or.inr h)

end Silmaril.Isotope.LetIter.Semantics
