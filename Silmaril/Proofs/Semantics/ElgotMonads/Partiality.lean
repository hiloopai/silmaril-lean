module

public import Silmaril.Semantics.ElgotMonads.Defs
import Batteries.Tactic.Alias

/-!
# Partiality and finite approximations: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

universe u

namespace Silmaril.Elgot.Part

variable {A B : Type u}

private theorem runs_of_mem_runFor {f : A → _root_.Part (B ⊕ A)} {fuel : Nat} {a : A} {b : B}
    (h : b ∈ runFor f fuel a) : Runs f a b := by
  induction fuel generalizing a with
  | zero => exact (_root_.Part.notMem_none b h).elim
  | succ fuel ih =>
      change b ∈ (f a).bind (Sum.elim _root_.Part.some (runFor f fuel)) at h
      rw [_root_.Part.mem_bind_iff] at h
      obtain ⟨s, hs, hb⟩ := h
      cases s with
      | inl b' =>
          have heq := _root_.Part.mem_some_iff.mp hb
          subst b'
          exact .done hs
      | inr a' => exact .more hs (ih hb)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runs_of_mem_runFor := Silmaril.Elgot.Part.runs_of_mem_runFor

private theorem Runs.exists_fuel {f : A → _root_.Part (B ⊕ A)} {a : A} {b : B}
    (h : Runs f a b) : ∃ fuel, b ∈ runFor f fuel a := by
  induction h with
  | @done a b hs =>
      refine ⟨1, ?_⟩
      change b ∈ (f a).bind (Sum.elim _root_.Part.some (runFor f 0))
      rw [_root_.Part.mem_bind_iff]
      exact ⟨.inl b, hs, _root_.Part.mem_some b⟩
  | @more a a' b hs _ ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      change b ∈ (f a).bind (Sum.elim _root_.Part.some (runFor f fuel))
      rw [_root_.Part.mem_bind_iff]
      exact ⟨.inr _, hs, hfuel⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.Runs.exists_fuel := Silmaril.Elgot.Part.Runs.exists_fuel

private theorem runFor_mono_succ (f : A → _root_.Part (B ⊕ A)) (fuel : Nat) (a : A) (b : B)
    (h : b ∈ runFor f fuel a) : b ∈ runFor f (fuel + 1) a := by
  induction fuel generalizing a with
  | zero => exact (_root_.Part.notMem_none b h).elim
  | succ fuel ih =>
      change b ∈ (f a).bind (Sum.elim _root_.Part.some (runFor f fuel)) at h
      change b ∈ (f a).bind (Sum.elim _root_.Part.some (runFor f (fuel + 1)))
      rw [_root_.Part.mem_bind_iff] at h ⊢
      obtain ⟨s, hs, hb⟩ := h
      refine ⟨s, hs, ?_⟩
      cases s with
      | inl _ => exact hb
      | inr _ => exact ih _ hb
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runFor_mono_succ := Silmaril.Elgot.Part.runFor_mono_succ

private theorem runFor_mono (f : A → _root_.Part (B ⊕ A)) {n k : Nat} (h : n ≤ k)
    (a : A) (b : B) : b ∈ runFor f n a → b ∈ runFor f k a := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hb => runFor_mono_succ f _ a b (ih hb)
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.runFor_mono := Silmaril.Elgot.Part.runFor_mono

private theorem iter_induction (f : A → _root_.Part (B ⊕ A)) (P : A → B → Prop)
    (done : ∀ a b, Sum.inl b ∈ f a → P a b)
    (more : ∀ a a' b, Sum.inr a' ∈ f a → P a' b → P a b)
    {a : A} {b : B} (h : b ∈ iter f a) : P a b := by
  rw [mem_iter_iff] at h
  induction h with
  | done hs => exact done _ _ hs
  | more hs _ ih => exact more _ _ _ hs ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.Part.iter_induction := Silmaril.Elgot.Part.iter_induction

end Silmaril.Elgot.Part
