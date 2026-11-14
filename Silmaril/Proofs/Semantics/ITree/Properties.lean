module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
public import Silmaril.Proofs.Semantics.ITree.Monad
public import Silmaril.Proofs.Semantics.ITree.Iteration
public import Silmaril.Proofs.Semantics.ITree.Laws
public import Silmaril.Proofs.Semantics.ITree.Codiagonal
import all Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Monad
import all Silmaril.Proofs.Semantics.ITree.Iteration
import all Silmaril.Proofs.Semantics.ITree.Laws
import all Silmaril.Proofs.Semantics.ITree.Codiagonal
import Batteries.Tactic.Alias

/-!
# Properties: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

universe u v

@[simp] private theorem diverge_bind {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E B) : (diverge >>= f) = diverge := by
  apply Tree.ext
  intro n
  cases n <;> simp [observe_bind, diverge, Approx.bind]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.diverge_bind := Silmaril.Elgot.ITree.diverge_bind

@[simp] private theorem vis_bind {E : Type u → Type u} {A B : Type v} {R : Type u}
    (e : E R) (k : R → Tree E A) (f : A → Tree E B) :
    (vis e k >>= f) = vis e (fun r => k r >>= f) := by
  apply Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [observe_bind, vis, Approx.bind, Part.bind_eq_bind, Part.bind_some]
    congr 2
    funext r
    congr 1
    funext a
    exact (f a).coherent n
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.vis_bind := Silmaril.Elgot.ITree.vis_bind

@[simp] private theorem iterate_done {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E B) :
    Silmaril.Elgot.iter (fun a => f a >>= pure ∘ Sum.inl) = f := by
  funext a
  rw [congrFun (iterate_fixpoint (fun a => f a >>= pure ∘ Sum.inl)) a]
  simp [LawfulMonad.bind_assoc]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.iterate_done := Silmaril.Elgot.ITree.iterate_done

@[simp] private theorem iterate_forever {E : Type u → Type u} {A B : Type v} (a : A) :
    Silmaril.Elgot.iter (fun a : A => (pure (.inr a) : Tree E (B ⊕ A))) a = diverge := by
  apply Tree.ext
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    show (Silmaril.Elgot.iter (fun a : A => (pure (.inr a) : Tree E (B ⊕ A))) a).observe (n + 1) =
      (diverge : Tree E B).observe (n + 1)
    let h : A → Approx E (B ⊕ A) (n + 1) := fun a => Part.some (.ret (.inr a))
    let point : ULift.{max (u + 1) v} Unit → Approx E (B ⊕ A) (n + 1) := fun _ => h a
    let loop : ULift.{max (u + 1) v} Unit → Part (Visible E B (Approx E B n) ⊕ ULift Unit) :=
      fun x => Part.some (.inr x)
    have comm : (loop >=> Silmaril.Elgot.liftPure (Sum.map id point)) =
        (Silmaril.Elgot.liftPure point >=> Approx.iterStep n h) := by
      funext x
      simp [Bind.kleisliRight, Silmaril.Elgot.liftPure, loop, point, h, Approx.iterStep]
    have simulation : Silmaril.Elgot.iter loop =
        (Silmaril.Elgot.liftPure point >=> Silmaril.Elgot.iter (Approx.iterStep n h)) :=
      Silmaril.Elgot.LawfulElgotMonad.uniformity loop (Approx.iterStep n h) point comm
    simpa [Bind.kleisliRight, Silmaril.Elgot.liftPure, Silmaril.Elgot.Part.iter_forever,
      observe_iter, Approx.iter_succ, loop, point, h, diverge, ret] using
      (congrFun simulation (ULift.up ())).symm
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.iterate_forever := Silmaril.Elgot.ITree.iterate_forever

private theorem iterate_pure_loop {E : Type u → Type u} {A B : Type v}
    (next : A → A) (a : A) :
    Silmaril.Elgot.iter (fun a => (pure (.inr (next a)) : Tree E (B ⊕ A))) a = diverge := by
  let point : A → PUnit.{v + 1} := fun _ => PUnit.unit
  have square :
      ((fun a => (pure (.inr (next a)) : Tree E (B ⊕ A))) >=>
        Elgot.liftPure (Sum.map id point)) =
      (Elgot.liftPure point >=> fun x => (pure (.inr x) : Tree E (B ⊕ PUnit.{v + 1}))) := by
    funext a
    simp [Bind.kleisliRight, Elgot.liftPure, point]
  have law := congrFun (Elgot.LawfulElgotMonad.uniformity
    (fun a => (pure (.inr (next a)) : Tree E (B ⊕ A)))
    (fun x => (pure (.inr x) : Tree E (B ⊕ PUnit.{v + 1}))) point square) a
  simpa only [Bind.kleisliRight, Elgot.liftPure, Function.comp_apply, pure_bind,
    iterate_forever] using law
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.iterate_pure_loop := Silmaril.Elgot.ITree.iterate_pure_loop

end Silmaril.Elgot.ITree
