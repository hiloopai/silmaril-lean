module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
public import Silmaril.Proofs.Semantics.ITree.Monad
public import Silmaril.Proofs.Semantics.ITree.Iteration
public import Silmaril.Proofs.Semantics.ITree.Laws
public import Silmaril.Proofs.Semantics.ITree.Codiagonal
public import Silmaril.Proofs.Semantics.ITree.Observe
public import Silmaril.Proofs.Semantics.ITree.Properties
import all Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Monad
import all Silmaril.Proofs.Semantics.ITree.Iteration
import all Silmaril.Proofs.Semantics.ITree.Laws
import all Silmaril.Proofs.Semantics.ITree.Codiagonal
import all Silmaril.Proofs.Semantics.ITree.Observe
import all Silmaril.Proofs.Semantics.ITree.Properties
import Batteries.Tactic.Alias

/-!
# Normalize: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

@[simp] private theorem resume_body (f : A → Tree E (B ⊕ A)) (a : A) :
    resume f (f a) = iter f a :=
  (congrFun (iterate_fixpoint f) a).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.resume_body := Silmaril.Elgot.ITree.resume_body

private theorem observe_resume (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) (n : Nat) :
    (resume f t).observe n =
      Approx.iter n (t.observe n) (fun a => (f a).observe n) := by
  rw [Approx.iter_fixpoint]
  change Approx.bind n (t.observe n) _ = _
  congr 1
  funext result
  cases result <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_resume := Silmaril.Elgot.ITree.observe_resume

private theorem normalizeStep_square (f : A → Tree E (B ⊕ A)) (n : Nat) :
    (mapReturn (normalizeStep f)
        (liftPure (Visible.map (fun t : Tree E B => t.observe n))) >=>
      liftPure (Sum.map id (fun t : Tree E (B ⊕ A) => t.observe (n + 1)))) =
      (liftPure (fun t : Tree E (B ⊕ A) => t.observe (n + 1)) >=>
        Approx.iterStep n (fun a => (f a).observe (n + 1))) := by
  funext t
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind,
    mapReturn, normalizeStep, Approx.iterStep]
  rw [observe_succ_eq_out t n]
  simp only [Part.map_eq_map, Part.bind_eq_bind, Part.bind_assoc, Part.bind_map]
  apply congrArg (Part.bind (out t))
  funext node
  cases node with
  | ret result =>
      cases result <;> simp [Visible.map, Function.comp_def, Part.pure_eq_some]
  | vis e next =>
      simp [Visible.map, Function.comp_def, Part.pure_eq_some]
      funext r
      rw [observe_resume]
      congr 1
      funext a
      exact ((f a).coherent n).symm

private theorem observe_normalize (f : A → Tree E (B ⊕ A))
    (t : Tree E (B ⊕ A)) (n : Nat) :
    Visible.map (fun child : Tree E B => child.observe n) <$>
        iter (normalizeStep f) t = (resume f t).observe (n + 1) := by
  have hn := congrFun (LawfulElgotMonad.naturality (m := Part)
    (normalizeStep f) (liftPure (Visible.map (fun child : Tree E B => child.observe n)))) t
  have hu := congrFun (LawfulElgotMonad.uniformity (m := Part)
    (mapReturn (normalizeStep f)
      (liftPure (Visible.map (fun child : Tree E B => child.observe n))))
    (Approx.iterStep n (fun a => (f a).observe (n + 1)))
    (fun t : Tree E (B ⊕ A) => t.observe (n + 1)) (normalizeStep_square f n)) t
  calc
    _ = (iter (normalizeStep f) >=>
        liftPure (Visible.map (fun child : Tree E B => child.observe n))) t := by
      exact (Part.bind_some_eq_map _ _).symm
    _ = iter (mapReturn (normalizeStep f)
        (liftPure (Visible.map (fun child : Tree E B => child.observe n)))) t := by
      exact hn
    _ = iter (Approx.iterStep n (fun a => (f a).observe (n + 1))) (t.observe (n + 1)) := by
      simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using hu
    _ = _ := by rw [observe_resume, Approx.iter_succ]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_normalize := Silmaril.Elgot.ITree.observe_normalize

private theorem out_resume (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A)) :
    out (resume f t) = iter (normalizeStep f) t := by
  apply roll_injective
  rw [roll_out]
  apply Tree.ext
  intro n
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact (observe_normalize f t n).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.out_resume := Silmaril.Elgot.ITree.out_resume

end Silmaril.Elgot.ITree
