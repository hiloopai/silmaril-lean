module

public import Silmaril.Semantics.ElgotMonads.Defs
import Batteries.Tactic.Alias

/-!
# Complete Elgot iteration with errors: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ExceptT

universe u

variable {m : Type u → Type u} [Monad m] {ε A B C : Type u}

@[simp] private theorem run_iter [Iterate m] (f : A → _root_.ExceptT ε m (B ⊕ A)) (a : A) :
    (iter f a).run = iter (body f) a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.run_iter := Silmaril.Elgot.ExceptT.run_iter

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

private theorem fixpoint (f : A → _root_.ExceptT ε m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) := by
  funext a
  apply _root_.ExceptT.ext
  rw [run_iter, _root_.ExceptT.run_bind, LawfulElgotMonad.fixpoint]
  simp only [body, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro x
  cases x with
  | error e => rfl
  | ok x => cases x <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.fixpoint := Silmaril.Elgot.ExceptT.fixpoint

omit [Iterate m] [LawfulElgotMonad m] in
private theorem body_mapReturn (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : B → _root_.ExceptT ε m C) :
    body (mapReturn f g) = mapReturn (body f) (extend g) := by
  funext a
  simp only [body, mapReturn, _root_.ExceptT.run_bind, Function.comp_apply,
    bind_assoc, pure_bind]
  apply bind_congr
  intro x
  cases x with
  | error e => simp [distribute, extend]
  | ok x =>
      cases x with
      | inr a => simp [distribute]
      | inl b =>
          simp only [Sum.elim_inl, _root_.ExceptT.run_bind, Function.comp_apply,
            _root_.ExceptT.run_pure, bind_assoc, distribute, extend]
          apply bind_congr
          intro y
          cases y <;> simp [distribute]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.body_mapReturn := Silmaril.Elgot.ExceptT.body_mapReturn

private theorem naturality (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : B → _root_.ExceptT ε m C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a
  apply _root_.ExceptT.ext
  simp only [Bind.kleisliRight, _root_.ExceptT.run_bind, run_iter]
  calc
    _ = iter (body f) a >>= extend g := by
      apply bind_congr
      intro x
      cases x <;> rfl
    _ = _ := by
      rw [body_mapReturn]
      exact congrFun (LawfulElgotMonad.naturality (body f) (extend g)) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.naturality := Silmaril.Elgot.ExceptT.naturality

private theorem body_iter (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    body (iter f) = iter (mapReturn (body f) (pure ∘ distribute)) :=
  LawfulElgotMonad.naturality (body f) (pure ∘ distribute)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.body_iter := Silmaril.Elgot.ExceptT.body_iter

omit [Iterate m] [LawfulElgotMonad m] in
private theorem body_flatten (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    flattenBody (mapReturn (body f) (pure ∘ distribute)) = body (flattenBody f) := by
  funext a
  simp only [flattenBody, Bind.kleisliRight, liftPure, mapReturn, body, Function.comp_apply,
    _root_.ExceptT.run_bind, _root_.ExceptT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro x
  cases x with
  | error e => simp [distribute, flatten]
  | ok x =>
      cases x with
      | inl x => cases x <;> simp [distribute, flatten]
      | inr x => simp [distribute, flatten]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.body_flatten := Silmaril.Elgot.ExceptT.body_flatten

private theorem codiagonal (f : A → _root_.ExceptT ε m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply _root_.ExceptT.ext
  change iter (body (iter f)) a = iter (body (flattenBody f)) a
  rw [body_iter, LawfulElgotMonad.codiagonal, body_flatten]
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.codiagonal := Silmaril.Elgot.ExceptT.codiagonal

private theorem uniformity (f : A → _root_.ExceptT ε m (B ⊕ A))
    (g : C → _root_.ExceptT ε m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) := by
  have square : (body f >=> liftPure (Sum.map id h)) = (liftPure h >=> body g) := by
    funext a
    calc
      _ = ((f >=> liftPure (Sum.map id h)) a).run >>= pure ∘ distribute := by
        simp only [Bind.kleisliRight, liftPure, body, Function.comp_apply, _root_.ExceptT.run_bind,
          _root_.ExceptT.run_pure, bind_assoc, pure_bind]
        apply bind_congr
        intro x
        cases x with
        | error e => simp [distribute]
        | ok x => cases x <;> simp [distribute]
      _ = ((liftPure h >=> g) a).run >>= pure ∘ distribute := by rw [comm]
      _ = _ := by simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, body]
  funext a
  apply _root_.ExceptT.ext
  simpa only [run_iter, Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using
    congrFun (LawfulElgotMonad.uniformity (body f) (body g) h square) a
alias _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.uniformity := Silmaril.Elgot.ExceptT.uniformity

instance _root_.Silmaril.Proofs.Semantics.Elgot.ExceptT.instLawfulElgotMonadExceptT : LawfulElgotMonad (_root_.ExceptT ε m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end Silmaril.Elgot.ExceptT
