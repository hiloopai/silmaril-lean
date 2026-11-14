module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import Batteries.Tactic.Alias

/-!
# Iteration with persistent finite and infinite output: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

private theorem observations_nonempty (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (observations f a).Nonempty := ⟨_, 1, a, .start a, rfl⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.observations_nonempty := Silmaril.Elgot.PartialWriter.observations_nonempty

variable [CompleteLattice W]

private theorem le_iterOutput {f : A → PartialWriter W (B ⊕ A)} {a z : A} {w : W}
    (h : Prefix f a w z) : w * (f z).output ≤ iterOutput f a :=
  le_sSup ⟨w, z, h, rfl⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.le_iterOutput := Silmaril.Elgot.PartialWriter.le_iterOutput

private theorem iterOutput_le {f : A → PartialWriter W (B ⊕ A)} {a : A} {v : W}
    (h : ∀ w z, Prefix f a w z → w * (f z).output ≤ v) : iterOutput f a ≤ v := by
  apply sSup_le
  rintro x ⟨w, z, hp, rfl⟩
  exact h w z hp
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_le := Silmaril.Elgot.PartialWriter.iterOutput_le

private theorem initial_le_iterOutput (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (f a).output ≤ iterOutput f a := by
  simpa only [one_mul] using le_iterOutput (Prefix.start (f := f) a)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.initial_le_iterOutput := Silmaril.Elgot.PartialWriter.initial_le_iterOutput

private theorem iterOutput_stop (f : A → PartialWriter W (B ⊕ A)) (a : A)
    (hstop : ∀ a', Sum.inr a' ∉ (f a).value) : iterOutput f a = (f a).output := by
  apply le_antisymm _ (initial_le_iterOutput f a)
  apply iterOutput_le
  intro w z h
  cases h with
  | start => simp
  | step hs _ => exact (hstop _ hs).elim
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_stop := Silmaril.Elgot.PartialWriter.iterOutput_stop

variable [ContinuousLog W]

private theorem iterOutput_step (f : A → PartialWriter W (B ⊕ A)) {a a' : A}
    (hs : Sum.inr a' ∈ (f a).value) :
    iterOutput f a = (f a).output * iterOutput f a' := by
  apply le_antisymm
  · apply iterOutput_le
    intro w z h
    cases h with
    | start => simpa only [one_mul] using ContinuousLog.le_mul_right (f a).output (iterOutput f a')
    | step ht hp =>
        have heq := Sum.inr.inj (_root_.Part.mem_unique hs ht)
        subst heq
        simpa only [mul_assoc] using ContinuousLog.mul_mono (le_refl (f a).output) (le_iterOutput hp)
  · rw [iterOutput, ContinuousLog.mul_sSup _ _ (observations_nonempty f a')]
    apply sSup_le
    rintro _ ⟨v, ⟨w, z, hp, rfl⟩, rfl⟩
    simpa only [mul_assoc] using le_iterOutput (Prefix.step hs hp)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_step := Silmaril.Elgot.PartialWriter.iterOutput_step

omit [ContinuousLog W] in
@[simp] private theorem value_iter (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (iter f a).value = iter (fun a => (f a).value) a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_iter := Silmaril.Elgot.PartialWriter.value_iter

omit [ContinuousLog W] in
@[simp] private theorem output_iter (f : A → PartialWriter W (B ⊕ A)) (a : A) :
    (iter f a).output = iterOutput f a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_iter := Silmaril.Elgot.PartialWriter.output_iter

private theorem fixpoint (f : A → PartialWriter W (B ⊕ A)) :
    iter f = fun a => f a >>= Sum.elim pure (iter f) := by
  funext a
  apply ext
  · simp only [value_iter, value_bind]
    rw [LawfulElgotMonad.fixpoint]
    apply bind_congr
    intro s
    cases s <;> rfl
  · rcases _root_.Part.eq_none_or_eq_some (f a).value with hn | ⟨s, hs⟩
    · rw [output_iter, iterOutput_stop f a (by simp [hn])]
      simp [bind, hn]
    · cases s with
      | inl b =>
          rw [output_iter, iterOutput_stop f a (by simp [hs])]
          simp [bind, hs, pure_def, done]
      | inr a' =>
          rw [output_iter, iterOutput_step f (_root_.Part.eq_some_iff.mp hs)]
          simp [bind, hs]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.fixpoint := Silmaril.Elgot.PartialWriter.fixpoint

private theorem Runs.iter_eq_done {f : A → PartialWriter W (B ⊕ A)} {a : A} {w : W} {b : B}
    (h : Runs f a w b) : iter f a = PartialWriter.done b w := by
  induction h with
  | done hs =>
      rw [fixpoint]
      dsimp only
      have hv := _root_.Part.eq_some_iff.mpr hs
      have hf : f _ = PartialWriter.done (.inl _) (f _).output := ext hv rfl
      rw [hf, bind_def, bind_done]
      simp [PartialWriter.done]
  | step hs _ ih =>
      rw [fixpoint]
      dsimp only
      have hv := _root_.Part.eq_some_iff.mpr hs
      have hf : f _ = PartialWriter.done (.inr _) (f _).output := ext hv rfl
      rw [hf, bind_def, bind_done]
      simp only [Sum.elim_inr, ih, PartialWriter.done]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.iter_eq_done := Silmaril.Elgot.PartialWriter.Runs.iter_eq_done

omit [ContinuousLog W] in
private theorem mem_value_iter_iff (f : A → PartialWriter W (B ⊕ A)) (a : A) (b : B) :
    b ∈ (iter f a).value ↔ ∃ w, Runs f a w b := by
  rw [value_iter, Part.mem_iter_iff, runs_value_iff]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_value_iter_iff := Silmaril.Elgot.PartialWriter.mem_value_iter_iff

end Silmaril.Elgot.PartialWriter
