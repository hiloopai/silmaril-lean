module

public import Silmaril.Semantics.TraceModels.Defs
import Batteries.Tactic.Alias

/-!
# Partial computations with persistent output: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot

universe u

namespace PartialWriter

variable {W A B C : Type u}

@[ext] private theorem ext {x y : PartialWriter W A}
    (hv : x.value = y.value) (hw : x.output = y.output) : x = y := by
  cases x
  cases y
  cases hv
  cases hw
  rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.ext := Silmaril.Elgot.PartialWriter.ext

@[elab_as_elim] private theorem cases_on (x : PartialWriter W A) {p : PartialWriter W A → Prop}
    (hdiverge : ∀ w, p (diverge w)) (hdone : ∀ a w, p (done a w)) : p x := by
  rcases x with ⟨value, output⟩
  induction value using _root_.Part.induction_on with
  | hnone => exact hdiverge output
  | hsome a => exact hdone a output
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.cases_on := Silmaril.Elgot.PartialWriter.cases_on

variable [Monoid W]

@[simp] private theorem bind_diverge (w : W) (f : A → PartialWriter W B) :
    bind (diverge w) f = diverge w := by
  simp [bind, diverge]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_diverge := Silmaril.Elgot.PartialWriter.bind_diverge

@[simp] private theorem bind_done (a : A) (w : W) (f : A → PartialWriter W B) :
    bind (done a w) f = ⟨(f a).value, w * (f a).output⟩ := by
  simp [bind, done]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_done := Silmaril.Elgot.PartialWriter.bind_done

@[simp] private theorem pure_def (a : A) : (pure a : PartialWriter W A) = done a 1 := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.pure_def := Silmaril.Elgot.PartialWriter.pure_def

@[simp] private theorem bind_def (x : PartialWriter W A) (f : A → PartialWriter W B) :
    x >>= f = bind x f := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_def := Silmaril.Elgot.PartialWriter.bind_def

@[simp] private theorem bind_pure (x : PartialWriter W A) : bind x (pure : A → PartialWriter W A) = x := by
  induction x using cases_on with
  | hdiverge w => simp
  | hdone a w => rw [bind_done]; simp [done]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_pure := Silmaril.Elgot.PartialWriter.bind_pure

@[simp] private theorem pure_bind (a : A) (f : A → PartialWriter W B) : bind (pure a) f = f a := by
  simp
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.pure_bind := Silmaril.Elgot.PartialWriter.pure_bind

private theorem bind_assoc (x : PartialWriter W A) (f : A → PartialWriter W B)
    (g : B → PartialWriter W C) : bind (bind x f) g = bind x (fun a => bind (f a) g) := by
  induction x using cases_on with
  | hdiverge w => simp
  | hdone a w =>
      simp only [bind_done]
      induction f a using cases_on with
      | hdiverge v => simp [diverge, bind]
      | hdone b v => simp [done, bind, mul_assoc]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.bind_assoc := Silmaril.Elgot.PartialWriter.bind_assoc

noncomputable instance _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.instLawfulMonad : LawfulMonad (PartialWriter W) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := fun x => bind_pure x)
  (pure_bind := pure_bind)
  (bind_assoc := bind_assoc)

@[simp] private theorem value_pure (a : A) : (pure a : PartialWriter W A).value = pure a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_pure := Silmaril.Elgot.PartialWriter.value_pure

@[simp] private theorem value_bind (x : PartialWriter W A) (f : A → PartialWriter W B) :
    (x >>= f).value = x.value >>= fun a => (f a).value := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_bind := Silmaril.Elgot.PartialWriter.value_bind

@[simp] private theorem output_pure (a : A) : (pure a : PartialWriter W A).output = 1 := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_pure := Silmaril.Elgot.PartialWriter.output_pure

@[simp] private theorem done_bind_diverge (a : A) (w v : W) :
    (done a w >>= fun _ => (diverge v : PartialWriter W B)) = diverge (w * v) := by
  simp [diverge]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.done_bind_diverge := Silmaril.Elgot.PartialWriter.done_bind_diverge

end PartialWriter

end Silmaril.Elgot
