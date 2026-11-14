module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Algebra
import Batteries.Tactic.Alias

/-!
# PartialWriter.Uniformity: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W]

variable (f : A → PartialWriter W (B ⊕ A)) (g : C → PartialWriter W (B ⊕ C))
    (h : A → C)
    (comm : (f >=> liftPure (Sum.map id h)) = (liftPure h >=> g))

include comm

private theorem uniform_value_comm :
    ((fun a => (f a).value) >=> liftPure (Sum.map id h)) =
      (liftPure h >=> fun c => (g c).value) := by
  funext a
  have e := congrArg PartialWriter.value (congrFun comm a)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_def, value_bind, value_pure,
    LawfulMonad.pure_bind] using e
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniform_value_comm := Silmaril.Elgot.PartialWriter.uniform_value_comm

private theorem uniform_output (a : A) : (f a).output = (g (h a)).output := by
  have e := congrArg PartialWriter.output (congrFun comm a)
  simpa only [Bind.kleisliRight, liftPure, bind_pure_comp, LawfulMonad.pure_bind,
    Function.comp_def, output_map] using e
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniform_output := Silmaril.Elgot.PartialWriter.uniform_output

private theorem Prefix.uniform_forward {a z : A} {w : W} (p : Prefix f a w z) :
    Prefix g (h a) w (h z) := by
  induction p with
  | start a => exact .start (h a)
  | step hs _ ih =>
      have hs' := (Part.uniform_step _ _ h (uniform_value_comm f g h comm) _ _).mpr
        ⟨.inr _, hs, rfl⟩
      simpa only [uniform_output f g h comm] using Prefix.step hs' ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.uniform_forward := Silmaril.Elgot.PartialWriter.Prefix.uniform_forward

private theorem Prefix.uniform_reverse {c z : C} {w : W} (p : Prefix g c w z) :
    ∀ a, c = h a → ∃ a', z = h a' ∧ Prefix f a w a' := by
  induction p with
  | start c =>
      intro a ha
      exact ⟨a, ha, .start a⟩
  | step hs _ ih =>
      intro a ha
      rw [ha] at hs
      rcases (Part.uniform_step _ _ h (uniform_value_comm f g h comm) a _).mp hs with
        ⟨s, hs', heq⟩
      cases s with
      | inl b => cases heq
      | inr a' =>
          rcases ih a' (Sum.inr.inj heq).symm with ⟨z', hz, hp⟩
          refine ⟨z', hz, ?_⟩
          simpa only [ha, uniform_output f g h comm] using Prefix.step hs' hp
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.uniform_reverse := Silmaril.Elgot.PartialWriter.Prefix.uniform_reverse

variable [CompleteLattice W]

private theorem uniformity : iter f = (liftPure h >=> iter g) := by
  funext a
  apply ext
  · simp only [Bind.kleisliRight, liftPure, Function.comp_def, LawfulMonad.pure_bind, value_iter]
    have hu := congrFun (Part.uniformity _ _ h (uniform_value_comm f g h comm)) a
    dsimp only [Bind.kleisliRight] at hu
    simpa only [liftPure, Function.comp_def, LawfulMonad.pure_bind] using hu
  · simp only [Bind.kleisliRight, liftPure, Function.comp_def, LawfulMonad.pure_bind, output_iter]
    apply le_antisymm
    · apply iterOutput_le
      intro w z hp
      rw [uniform_output f g h comm]
      exact le_iterOutput (hp.uniform_forward f g h comm)
    · apply iterOutput_le
      intro w z hp
      rcases hp.uniform_reverse f g h comm a rfl with ⟨z', hz, hp'⟩
      rw [hz, ← uniform_output f g h comm]
      exact le_iterOutput hp'
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.uniformity := Silmaril.Elgot.PartialWriter.uniformity

end Silmaril.Elgot.PartialWriter
