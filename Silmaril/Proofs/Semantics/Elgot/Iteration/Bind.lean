module

public import Silmaril.Semantics.Elgot.Defs
public import Silmaril.Proofs.Semantics.Elgot.Basic
import all Silmaril.Proofs.Semantics.Elgot.Basic
import Batteries.Tactic.Alias

/-!
# Iteration.Bind: proofs

Proofs for `Silmaril.Semantics.Elgot.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u v

variable {m : Type u → Type v} [Monad m]

variable {A B : Type u}

variable [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

@[simp] private theorem iter_bindBody_inr (x : m A) (f : A → m B) (a : A) :
    iter (bindBody x f) (.inr a) = f a := by
  rw [congrFun (LawfulElgotMonad.fixpoint (bindBody x f)) (.inr a)]
  simp [bindBody]
alias _root_.Silmaril.Proofs.Semantics.Elgot.iter_bindBody_inr := Silmaril.Elgot.iter_bindBody_inr

private theorem bind_eq_iter (x : m A) (f : A → m B) :
    (x >>= f) = iter (bindBody x f) (.inl PUnit.unit) := by
  rw [congrFun (LawfulElgotMonad.fixpoint (bindBody x f)) (.inl PUnit.unit)]
  simp [bindBody]
alias _root_.Silmaril.Proofs.Semantics.Elgot.bind_eq_iter := Silmaril.Elgot.bind_eq_iter

end Silmaril.Elgot
