module

public import Silmaril.Semantics.Elgot.Defs
public import Silmaril.Proofs.Semantics.Elgot.Basic
public import Silmaril.Proofs.Semantics.Elgot.Iteration.Bind
import all Silmaril.Proofs.Semantics.Elgot.Basic
import all Silmaril.Proofs.Semantics.Elgot.Iteration.Bind
import Batteries.Tactic.Alias

/-!
# Iteration.MonadMap: proofs

Proofs for `Silmaril.Semantics.Elgot.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u v w

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

variable {n : Type u → Type w} [Monad n] [LawfulMonad n] [Iterate n] [LawfulElgotMonad n]

private theorem map_bind_of_map_iter (map : {A : Type u} → m A → n A)
    (map_map : ∀ {A B : Type u} (x : m A) (f : A → B),
      map (x >>= pure ∘ f) = (map x >>= pure ∘ f))
    (map_iter : ∀ {A B : Type u} (f : A → m (B ⊕ A)) (a : A),
      map (iter f a) = iter (fun a => map (f a)) a)
    {A B : Type u} (x : m A) (f : A → m B) :
    map (x >>= f) = (map x >>= fun a => map (f a)) := by
  rw [bind_eq_iter x f, map_iter, bind_eq_iter (map x) (fun a => map (f a))]
  congr 1
  funext phase
  cases phase with
  | inl _ => exact map_map x (fun a => (Sum.inr (Sum.inr a) : B ⊕ (PUnit.{u + 1} ⊕ A)))
  | inr a => exact map_map (f a) Sum.inl
alias _root_.Silmaril.Proofs.Semantics.Elgot.map_bind_of_map_iter := Silmaril.Elgot.map_bind_of_map_iter

end Silmaril.Elgot
