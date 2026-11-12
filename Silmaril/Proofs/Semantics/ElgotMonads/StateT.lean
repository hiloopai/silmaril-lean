module

public import Silmaril.Semantics.ElgotMonads.Defs
import Batteries.Tactic.Alias

/-!
# Complete Elgot iteration through mutable state: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.StateT

universe u v

variable {m : Type u → Type v} [Monad m] {σ A B C : Type u}

@[simp] private theorem run_iter [Iterate m] (f : A → _root_.StateT σ m (B ⊕ A)) (a : A) (s : σ) :
    (iter f a).run s = iter (body f) (a, s) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.run_iter := Silmaril.Elgot.StateT.run_iter

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

private theorem fixpoint (f : A → _root_.StateT σ m (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) := by
  funext a
  apply _root_.StateT.ext
  intro s
  rw [run_iter, _root_.StateT.run_bind]
  rw [LawfulElgotMonad.fixpoint (body f)]
  simp only [body, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  rintro ⟨x, s'⟩
  cases x <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.fixpoint := Silmaril.Elgot.StateT.fixpoint

omit [Iterate m] [LawfulElgotMonad m] in
private theorem body_mapReturn (f : A → _root_.StateT σ m (B ⊕ A))
    (g : B → _root_.StateT σ m C) :
    body (mapReturn f g) = mapReturn (body f) (fun p => (g p.1).run p.2) := by
  funext ⟨a, s⟩
  simp only [body, mapReturn, Function.comp_apply, _root_.StateT.run_bind,
    bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨x, s'⟩
  cases x <;> simp [distribute, _root_.StateT.run_bind, -bind_pure_comp]
  apply bind_congr
  rintro ⟨b, s''⟩
  rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.body_mapReturn := Silmaril.Elgot.StateT.body_mapReturn

private theorem naturality (f : A → _root_.StateT σ m (B ⊕ A))
    (g : B → _root_.StateT σ m C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a s
  change (iter (body f) (a, s) >>= fun p => g p.1 p.2) = iter (body (mapReturn f g)) (a, s)
  rw [body_mapReturn]
  exact congrFun (LawfulElgotMonad.naturality (body f) (fun p => g p.1 p.2)) (a, s)
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.naturality := Silmaril.Elgot.StateT.naturality

private theorem body_iter (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    body (iter f) = iter (mapReturn (body f) (pure ∘ distribute)) :=
  LawfulElgotMonad.naturality (body f) (pure ∘ distribute)
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.body_iter := Silmaril.Elgot.StateT.body_iter

omit [Iterate m] [LawfulElgotMonad m] in
private theorem body_flatten (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    flattenBody (mapReturn (body f) (pure ∘ distribute)) = body (flattenBody f) := by
  funext ⟨a, s⟩
  simp only [flattenBody, Bind.kleisliRight, liftPure, mapReturn, body, Function.comp_apply,
    _root_.StateT.run_bind, _root_.StateT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨x, s'⟩
  cases x with
  | inl x => cases x <;> simp [distribute, flatten]
  | inr x => simp [distribute, flatten]
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.body_flatten := Silmaril.Elgot.StateT.body_flatten

private theorem codiagonal (f : A → _root_.StateT σ m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a s
  change iter (body (iter f)) (a, s) = iter (body (flattenBody f)) (a, s)
  rw [body_iter, LawfulElgotMonad.codiagonal, body_flatten]
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.codiagonal := Silmaril.Elgot.StateT.codiagonal

private theorem distribute_map (h : A → C) (p : (B ⊕ A) × σ) :
    Sum.map id (Prod.map h id) (distribute p) = distribute (Sum.map id h p.1, p.2) := by
  rcases p with ⟨x, s⟩
  cases x <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.distribute_map := Silmaril.Elgot.StateT.distribute_map

private theorem uniformity (f : A → _root_.StateT σ m (B ⊕ A))
    (g : C → _root_.StateT σ m (B ⊕ C)) (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g)) :
    iter f = (liftPure h >=> iter g) := by
  have square : (body f >=> liftPure (Sum.map id (Prod.map h id))) =
      (liftPure (Prod.map h id) >=> body g) := by
    funext ⟨a, s⟩
    have hs := congrArg (fun z : _root_.StateT σ m (B ⊕ C) => z.run s >>= pure ∘ distribute)
      (congrFun comm a)
    simpa only [Bind.kleisliRight, liftPure, body, Function.comp_apply, _root_.StateT.run_bind,
      _root_.StateT.run_pure, bind_assoc, pure_bind, distribute_map, Prod.map, id_eq] using hs
  funext a
  apply _root_.StateT.ext
  intro s
  simp only [run_iter, Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, Prod.map, id_eq] using
    congrFun (LawfulElgotMonad.uniformity (body f) (body g) (Prod.map h id) square) (a, s)
alias _root_.Silmaril.Proofs.Semantics.Elgot.StateT.uniformity := Silmaril.Elgot.StateT.uniformity

instance _root_.Silmaril.Proofs.Semantics.Elgot.StateT.instLawfulElgotMonadStateT : LawfulElgotMonad (_root_.StateT σ m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end Silmaril.Elgot.StateT
