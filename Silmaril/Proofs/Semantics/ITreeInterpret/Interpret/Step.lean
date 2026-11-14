module

public import Silmaril.Semantics.ITreeInterpret.Defs
public import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Partial
import all Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Partial
import Batteries.Tactic.Alias

/-!
# Interpret.Step: proofs

Proofs for `Silmaril.Semantics.ITreeInterpret.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

@[simp] private theorem fold_diverge {A : Type u} [Small.{u} (Tree E A)]
    (handler : Handler E m) : fold (E := E) (m := m) handler (diverge : Tree E A) = bottom := by
  exact iter_of_pure_self _ _ (by simp)
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.fold_diverge := Silmaril.Elgot.ITree.Interpret.fold_diverge

end Silmaril.Elgot.ITree.Interpret
