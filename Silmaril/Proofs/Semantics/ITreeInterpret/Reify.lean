module

public import Silmaril.Semantics.ITreeInterpret.Defs
import Batteries.Tactic.Alias

/-!
# Reify: proofs

Proofs for `Silmaril.Semantics.ITreeInterpret.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree.Interpret

universe u

variable {E : Type u → Type u} {A : Type u} [Small.{u} (Tree E A)]

@[simp] private theorem fold_self_diverge :
    fold (E := E) (m := Tree E) trigger (diverge : Tree E A) = diverge := by
  let point : PUnit.{u + 1} → Shrink.{u} (Tree E A) := fun _ => equivShrink _ diverge
  have square :
      ((fun p : PUnit.{u + 1} => (pure (.inr p) : Tree E (A ⊕ PUnit.{u + 1}))) >=>
        liftPure (Sum.map id point)) =
      (liftPure point >=> step (E := E) (m := Tree E) trigger) := by
    funext p
    simp [Bind.kleisliRight, liftPure, point]
  have eq := congrFun (LawfulElgotMonad.uniformity
    (fun p : PUnit.{u + 1} => (pure (.inr p) : Tree E (A ⊕ PUnit.{u + 1})))
    (step (E := E) (m := Tree E) trigger) point square) PUnit.unit
  simpa [Bind.kleisliRight, liftPure, point, fold] using eq.symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_self_diverge := Silmaril.Elgot.ITree.Interpret.fold_self_diverge

@[simp] private theorem fold_self (t : Tree E A) :
    fold (E := E) (m := Tree E) trigger t = t := by
  apply Tree.ext
  intro n
  induction n generalizing t with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      rcases cases_visible t with h | ⟨a, h⟩ | ⟨R, e, next, h⟩
      · rw [h, fold_self_diverge]
      · rw [h, fold_ret]
        rfl
      · rw [h, fold_vis]
        simp only [trigger, vis_bind]
        have pure_eq : (ret (E := E) : R → Tree E R) = pure := rfl
        simp only [pure_eq, pure_bind]
        change Part.some (Visible.vis (A := A) e (fun r =>
          (fold (E := E) (m := Tree E) trigger (next r)).observe n)) =
          Part.some (Visible.vis (A := A) e (fun r => (next r).observe n))
        congr 2
        funext r
        exact ih (next r)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_self := Silmaril.Elgot.ITree.Interpret.fold_self

end Silmaril.Elgot.ITree.Interpret
