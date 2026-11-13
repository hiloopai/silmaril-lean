module

import all Init.While
public import Silmaril.Foundations.InfiniteTrace.Deterministic

/-! # Logical unfolding of identity-monad loops

`repeatM` pins its opaque implementation to a fixed point when one exists.
For deterministic identity-monad iteration a fixed point always exists: choose
the unique reachable terminal value, or an arbitrary value if none is reachable.
This supplies a proof-producing evaluator with the unfolding equation needed to
check a concrete execution of the existing Mir linker's fuel-bounded while loop.
-/

@[expose] public section

namespace Silmaril.Compile.Mir.WhileId

open Relation

universe u
variable {α β : Type u}

private def Next (f : α → α ⊕ β) (a a' : α) : Prop := f a = .inl a'
private def Terminal (f : α → α ⊕ β) (a : α) (b : β) : Prop :=
  ∃ t, ReflTransGen (Next f) a t ∧ f t = .inr b

private theorem terminal_unique {f : α → α ⊕ β} {a : α} {b c : β}
    (hb : Terminal f a b) (hc : Terminal f a c) : b = c := by
  obtain ⟨t, ht, hbt⟩ := hb
  obtain ⟨u, hu, hcu⟩ := hc
  have hR : Relator.RightUnique (Next f) := by
    intro x y z hy hz
    exact Sum.inl.inj (hy.symm.trans hz)
  have htf : ∀ x, ¬ Next f t x := by
    intro x hx
    simp only [Next, hbt, Sum.inr_ne_inl] at hx
  have huf : ∀ x, ¬ Next f u x := by
    intro x hx
    simp only [Next, hcu, Sum.inr_ne_inl] at hx
  obtain rfl := RightUnique.reach_final_eq hR ht hu htf huf
  exact Sum.inr.inj (hbt.symm.trans hcu)

private theorem terminal_next {f : α → α ⊕ β} {a a' : α}
    (ha : f a = .inl a') (b : β) : Terminal f a b ↔ Terminal f a' b := by
  constructor
  · rintro ⟨t, ht, hbt⟩
    rcases ht.cases_head with he | ⟨u, hu, hut⟩
    · subst t
      rw [ha] at hbt
      cases hbt
    · have he : a' = u := Sum.inl.inj (ha.symm.trans hu)
      subst u
      exact ⟨t, hut, hbt⟩
  · rintro ⟨t, ht, hbt⟩
    exact ⟨t, ht.head ha, hbt⟩

private noncomputable def result [Nonempty β] (f : α → α ⊕ β) (a : α) : β :=
  open scoped Classical in
  if h : ∃ b, Terminal f a b then h.choose else Classical.ofNonempty

private theorem result_terminal [Nonempty β] {f : α → α ⊕ β} {a : α} {b : β}
    (hb : Terminal f a b) : result f a = b := by
  classical
  unfold result
  rw [dite_eq_left ⟨b, hb⟩]
  exact terminal_unique (Exists.choose_spec ⟨b, hb⟩) hb

/-- Every identity-monad iteration has a logical fixed point. Diverging orbits
may choose any value; finite orbits have their unique terminal value. -/
private theorem fixed_point [Nonempty β] (f : α → Id (α ⊕ β)) :
    ∃ g : α → Id β, repeatM.body (m := Id) f g = g := by
  classical
  refine ⟨result f, funext fun a => ?_⟩
  change (match f a with | .inl a' => result f a' | .inr b => b) = result f a
  cases ha : f a with
  | inl a' =>
    have he : Terminal f a = Terminal f a' :=
      funext fun b => propext (terminal_next ha b)
    simp only [result, he]
  | inr b =>
    exact (result_terminal ⟨a, .refl, ha⟩).symm

/-- The ordinary loop equation, proved for `Id` without evaluating its opaque
implementation or adding a compiler trust assumption. -/
theorem repeatM_eq [Nonempty β] (f : α → Id (α ⊕ β)) (a : α) :
    repeatM (m := Id) f a = repeatM.body (m := Id) f (repeatM (m := Id) f) a :=
  _root_.repeatM_eq (m := Id) a (fixed_point f)

#print axioms repeatM_eq

end Silmaril.Compile.Mir.WhileId
