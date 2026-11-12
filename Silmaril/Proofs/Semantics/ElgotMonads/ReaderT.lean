module

public import Silmaril.Semantics.ElgotMonads.Defs
import Batteries.Tactic.Alias

/-!
# ReaderT: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ReaderT

universe u

variable {m : Type u → Type u} [Monad m] {ρ A B C : Type u}

omit [Monad m] in
@[simp] private theorem run_iter [Iterate m] (f : A → _root_.ReaderT ρ m (B ⊕ A)) (a : A) (r : ρ) :
    (iter f a).run r = iter (fun a => (f a).run r) a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.run_iter := Silmaril.Elgot.ReaderT.run_iter

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

private theorem fixpoint (f : A → _root_.ReaderT ρ m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) := by
  funext a
  apply _root_.ReaderT.ext
  intro r
  rw [run_iter, _root_.ReaderT.run_bind, LawfulElgotMonad.fixpoint]
  apply bind_congr
  intro x
  cases x <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.fixpoint := Silmaril.Elgot.ReaderT.fixpoint

omit [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] in
private theorem run_mapReturn (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : B → _root_.ReaderT ρ m C) (r : ρ) :
    (fun a => (mapReturn f g a).run r) =
      mapReturn (fun a => (f a).run r) (fun b => (g b).run r) := by
  funext a
  simp only [mapReturn, _root_.ReaderT.run_bind]
  apply bind_congr
  intro x
  cases x <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.run_mapReturn := Silmaril.Elgot.ReaderT.run_mapReturn

private theorem naturality (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : B → _root_.ReaderT ρ m C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a
  apply _root_.ReaderT.ext
  intro r
  simp only [Bind.kleisliRight, _root_.ReaderT.run_bind, run_iter, run_mapReturn]
  exact congrFun (LawfulElgotMonad.naturality (fun a => (f a).run r)
    (fun b => (g b).run r)) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.naturality := Silmaril.Elgot.ReaderT.naturality

private theorem codiagonal (f : A → _root_.ReaderT ρ m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply _root_.ReaderT.ext
  intro r
  change iter (iter (fun a => (f a).run r)) a =
    iter (flattenBody (fun a => (f a).run r)) a
  exact congrFun (LawfulElgotMonad.codiagonal (fun a => (f a).run r)) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.codiagonal := Silmaril.Elgot.ReaderT.codiagonal

private theorem uniformity (f : A → _root_.ReaderT ρ m (B ⊕ A))
    (g : C → _root_.ReaderT ρ m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) := by
  funext a
  apply _root_.ReaderT.ext
  intro r
  have square : ((fun a => (f a).run r) >=> liftPure (Sum.map id h)) =
      (liftPure h >=> fun c => (g c).run r) := by
    funext a
    simpa only [Bind.kleisliRight, liftPure, Function.comp_def, _root_.ReaderT.run_bind,
      _root_.ReaderT.run_pure, pure_bind] using congrArg (fun x => x.run r) (congrFun comm a)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, run_iter] using
    congrFun (LawfulElgotMonad.uniformity (fun a => (f a).run r) (fun c => (g c).run r)
      h square) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.uniformity := Silmaril.Elgot.ReaderT.uniformity

instance _root_.Silmaril.Proofs.Semantics.Elgot.ReaderT.instLawfulElgotMonadReaderT : LawfulElgotMonad (_root_.ReaderT ρ m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end Silmaril.Elgot.ReaderT
