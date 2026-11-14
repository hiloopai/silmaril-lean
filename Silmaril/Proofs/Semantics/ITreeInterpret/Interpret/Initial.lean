module

public import Silmaril.Semantics.ITreeInterpret.Defs
public import Silmaril.Proofs.Semantics.ITreeInterpret.Reify
public import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Hom
public import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Partial
public import Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Step
import all Silmaril.Proofs.Semantics.ITreeInterpret.Reify
import all Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Hom
import all Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Partial
import all Silmaril.Proofs.Semantics.ITreeInterpret.Interpret.Step
import Batteries.Tactic.Alias

/-!
# Interpret.Initial: proofs

Proofs for `Silmaril.Semantics.ITreeInterpret.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {E : Type u → Type u} [∀ A : Type u, Small.{u} (Tree E A)]
  {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

private theorem initial (handler : Handler E m) : ∃! _f : Hom (E := E) (m := m) handler, True := by
  refine ⟨foldHom (E := E) (m := m) handler, trivial, ?_⟩
  intro candidate _
  apply Hom.ext
  intro A t
  exact candidate.unique t
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.initial := Silmaril.Elgot.ITree.Interpret.initial

end Silmaril.Elgot.ITree.Interpret
