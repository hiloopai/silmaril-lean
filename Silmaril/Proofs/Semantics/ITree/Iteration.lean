module

public import Silmaril.Semantics.ITree.Defs
public import Silmaril.Proofs.Semantics.ITree.Basic
public import Silmaril.Proofs.Semantics.ITree.Monad
import all Silmaril.Proofs.Semantics.ITree.Basic
import all Silmaril.Proofs.Semantics.ITree.Monad
import Batteries.Tactic.Alias

/-!
# Iteration: proofs

Proofs for `Silmaril.Semantics.ITree.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree

open Silmaril.Elgot

universe u v

namespace Approx

end Approx

@[simp] private theorem observe_iter {E : Type u → Type u} {A B : Type v}
    (f : A → Tree E (B ⊕ A)) (a : A) (n : Nat) :
    (Silmaril.Elgot.iter f a).observe n =
      Approx.iter n ((f a).observe n) (fun a => (f a).observe n) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.observe_iter := Silmaril.Elgot.ITree.observe_iter

end Silmaril.Elgot.ITree
