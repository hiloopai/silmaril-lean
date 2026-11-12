module

public import Silmaril.Semantics.ElgotMonads.Defs
public import Silmaril.Proofs.Semantics.ElgotMonads.StateT
import all Silmaril.Proofs.Semantics.ElgotMonads.StateT
import Batteries.Tactic.Alias

/-!
# Writer iteration over an Elgot monad: proofs

Proofs for `Silmaril.Semantics.ElgotMonads.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.WriterT

universe u

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  {W A B : Type u} [Monoid W]

omit [LawfulMonad m] in
@[simp] private theorem run_iter [Iterate m] (f : A → _root_.WriterT W m (B ⊕ A)) (a : A) :
    (iter f a).run = iter (body f) (a, 1) := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.WriterT.run_iter := Silmaril.Elgot.WriterT.run_iter

variable [Iterate m] [LawfulElgotMonad m]

section Examples

private theorem twoSteps_run {W : Type} [Monoid W] (first second : W) :
    (iter (twoSteps first second) false).run = _root_.Part.some (PUnit.unit, first * second) := by
  apply _root_.Part.eq_some_iff.mpr
  rw [run_iter, Part.mem_iter_iff]
  apply Part.Runs.more (a' := (true, first))
  · simp [body, StateT.body, toState, _root_.StateT.run, twoSteps, StateT.distribute]
  · apply Part.Runs.done
    simp [body, StateT.body, toState, _root_.StateT.run, twoSteps, StateT.distribute]
alias _root_.Silmaril.Proofs.Semantics.Elgot.WriterT.twoSteps_run := Silmaril.Elgot.WriterT.twoSteps_run

private theorem forever_run (w : W) (a : A) :
    (iter (B := B) (fun a : A =>
      _root_.WriterT.mk (_root_.Part.some (Sum.inr a, w))) a).run = _root_.Part.none := by
  apply _root_.Part.eq_none_iff.mpr
  intro p hp
  rw [run_iter, Part.mem_iter_iff] at hp
  generalize (a, (1 : W)) = start at hp
  induction hp with
  | done hs =>
      simp [body, StateT.body, toState, _root_.StateT.run, StateT.distribute] at hs
  | more _ _ ih => exact ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.WriterT.forever_run := Silmaril.Elgot.WriterT.forever_run

end Examples

end Silmaril.Elgot.WriterT
