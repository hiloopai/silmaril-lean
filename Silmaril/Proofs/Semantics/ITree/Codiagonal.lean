module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
public import Silmaril.Proofs.Semantics.ITree.Monad
public import Silmaril.Proofs.Semantics.ITree.Iteration
public import Silmaril.Proofs.Semantics.ITree.Laws
import all Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Monad
import all Silmaril.Proofs.Semantics.ITree.Iteration
import all Silmaril.Proofs.Semantics.ITree.Laws
import Batteries.Tactic.Alias

/-!
# Codiagonal: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

private theorem doubleStep_eq_mapReturn {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    doubleStep n f = Silmaril.Elgot.mapReturn (iterStep n f) (doublePost n f) := by
  funext x
  simp only [doubleStep, Silmaril.Elgot.mapReturn, iterStep, LawfulMonad.bind_assoc]
  apply congrArg (x >>= ·)
  funext node
  cases node with
  | ret s => cases s with
    | inl s => cases s <;> simp [doublePost]
    | inr a => simp
  | vis e next => simp [doublePost]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_eq_mapReturn := Silmaril.Elgot.ITree.Approx.doubleStep_eq_mapReturn

private theorem doubleStep_inner_square {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1)) :
    (Silmaril.Elgot.iter (doubleStep n f) >=>
      liftPure (Sum.map id (fun x => iter (n + 1) x f))) =
    (liftPure (fun x => iter (n + 1) x f) >=>
      iterStep n (fun a => iter (n + 1) (f a) f)) := by
  rw [doubleStep_eq_mapReturn, ← LawfulElgotMonad.naturality]
  funext x
  simp only [Bind.kleisliRight, liftPure, Function.comp_apply, LawfulMonad.pure_bind, LawfulMonad.bind_assoc]
  unfold iterStep
  apply congrArg (iter (n + 1) x f >>= ·)
  funext node
  cases node with
  | ret s => cases s <;> simp [doublePost]
  | vis e next =>
      simp [doublePost]
      funext r
      congr 1
      funext a
      exact (truncate_iter n (f a) f).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_inner_square := Silmaril.Elgot.ITree.Approx.doubleStep_inner_square

private theorem doubleStep_flatten_square {E : Type u → Type u} {A B : Type v}
    (n : Nat) (f : A → Approx E ((B ⊕ A) ⊕ A) (n + 1))
    (ih : ∀ x, iter n (iter n x (fun a => truncate n (f a)))
        (fun a => iter n (truncate n (f a)) (fun a => truncate n (f a))) =
      iter n (flattenApprox n x) (fun a => flattenApprox n (truncate n (f a)))) :
    (Silmaril.Elgot.flattenBody (doubleStep n f) >=>
      liftPure (Sum.map id (flattenApprox (E := E) (A := A) (B := B) (n + 1)))) =
    (liftPure (flattenApprox (E := E) (A := A) (B := B) (n + 1)) >=>
      iterStep n (fun a => flattenApprox (n + 1) (f a))) := by
  funext x
  simp only [Silmaril.Elgot.flattenBody, Bind.kleisliRight, liftPure, Function.comp_apply,
    doubleStep, flattenApprox, bind, iterStep, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
  apply congrArg (x >>= ·)
  funext node
  cases node with
  | ret s => cases s with
    | inl s => cases s <;> simp [Silmaril.Elgot.flatten, ret]; rfl
    | inr a => simp [Silmaril.Elgot.flatten, ret]; rfl
  | vis e next =>
      simp [Silmaril.Elgot.flatten]
      funext r
      rw [ih (next r)]
      congr 1
      · unfold flattenApprox
        congr 1
        funext s
        exact ((ret (E := E) (Silmaril.Elgot.flatten s)).coherent n).symm
      · funext a
        exact (truncate_flattenApprox n (f a)).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.doubleStep_flatten_square := Silmaril.Elgot.ITree.Approx.doubleStep_flatten_square

private theorem iter_codiagonal {E : Type u → Type u} {A B : Type v}
    (n : Nat) (x : Approx E ((B ⊕ A) ⊕ A) n)
    (f : A → Approx E ((B ⊕ A) ⊕ A) n) :
    iter n (iter n x f) (fun a => iter n (f a) f) =
      iter n (flattenApprox n x) (fun a => flattenApprox n (f a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have inner := LawfulElgotMonad.uniformity (m := Part)
        (Silmaril.Elgot.iter (doubleStep n f))
        (iterStep n (fun a => iter (n + 1) (f a) f))
        (fun x => iter (n + 1) x f) (doubleStep_inner_square n f)
      have flattened := LawfulElgotMonad.uniformity (m := Part)
        (Silmaril.Elgot.flattenBody (doubleStep n f))
        (iterStep n (fun a => flattenApprox (n + 1) (f a)))
        (flattenApprox (n + 1))
        (doubleStep_flatten_square n f (fun y => ih y (fun a => truncate n (f a))))
      calc
        _ = Silmaril.Elgot.iter (Silmaril.Elgot.iter (doubleStep n f)) x := by
          simpa [Bind.kleisliRight, liftPure] using (congrFun inner x).symm
        _ = Silmaril.Elgot.iter (Silmaril.Elgot.flattenBody (doubleStep n f)) x :=
          congrFun (LawfulElgotMonad.codiagonal (doubleStep n f)) x
        _ = _ := by simpa [Bind.kleisliRight, liftPure] using congrFun flattened x
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Approx.iter_codiagonal := Silmaril.Elgot.ITree.Approx.iter_codiagonal

end Approx

@[simp] private theorem observe_flattenBody {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E ((B ⊕ A) ⊕ A)) (a : A) (n : Nat) :
    (Silmaril.Elgot.flattenBody f a).observe n =
      Approx.flattenApprox n ((f a).observe n) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_flattenBody := Silmaril.Elgot.ITree.observe_flattenBody

private theorem iterate_codiagonal {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E ((B ⊕ A) ⊕ A)) :
    Silmaril.Elgot.iter (Silmaril.Elgot.iter f) =
      Silmaril.Elgot.iter (Silmaril.Elgot.flattenBody f) := by
  funext a
  apply Tree.ext
  intro n
  simp only [observe_iter, observe_flattenBody]
  exact Approx.iter_codiagonal n ((f a).observe n) (fun a => (f a).observe n)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.iterate_codiagonal := Silmaril.Elgot.ITree.iterate_codiagonal

noncomputable instance _root_.Silmaril.Proofs.Semantics.Elgot.ITree.instLawfulElgotMonad (E : Type u → Type u) :
    LawfulElgotMonad (Tree E) where
  fixpoint := iterate_fixpoint
  naturality := iterate_naturality
  codiagonal := iterate_codiagonal
  uniformity := iterate_uniformity

end Silmaril.Elgot.ITree
