module

public import Silmaril.Semantics.ITreeInterpret.Defs
import Batteries.Tactic.Alias

/-!
# Interpret.Partial: proofs

Proofs for `Silmaril.Semantics.ITreeInterpret.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.ITree.Interpret

universe u v

variable {m : Type u → Type v} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

private theorem liftPart_bind {A B : Type u} (x : _root_.Part A) (k : A → _root_.Part B) :
    liftPart (m := m) (x >>= k) = (liftPart (m := m) x >>= fun a => liftPart (m := m) (k a)) := by
  induction x using _root_.Part.induction_on with
  | hnone => simp
  | hsome a => simp
alias _root_.Silmaril.Proofs.Semantics.Elgot.ITree.Interpret.liftPart_bind := Silmaril.Elgot.ITree.Interpret.liftPart_bind

end Silmaril.Elgot.ITree.Interpret
