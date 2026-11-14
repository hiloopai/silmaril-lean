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
# PartialWriter.Naturality: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W] [CompleteLattice W] [ContinuousLog W]

private theorem Runs.iter_mapReturn {f : A → PartialWriter W (B ⊕ A)}
    {a : A} {w : W} {b : B} (h : Runs f a w b) (g : B → PartialWriter W C) :
    iter (mapReturn f g) a = PartialWriter.done b w >>= g := by
  induction h with
  | done hs =>
      rw [fixpoint]
      dsimp only
      have hf : f _ = PartialWriter.done (.inl _) (f _).output :=
        ext (_root_.Part.eq_some_iff.mpr hs) rfl
      rw [mapReturn, hf]
      simp only [bind_def, bind_done, Sum.elim_inl]
      induction g _ using cases_on with
      | hdiverge v => simp [bind, PartialWriter.done, diverge]
      | hdone c v => simp [bind, PartialWriter.done]
  | step hs _ ih =>
      rw [fixpoint]
      dsimp only
      rw [mapReturn_inr f g hs]
      simp only [bind_def, bind_done, Sum.elim_inr, ih]
      simp [mul_assoc]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.iter_mapReturn := Silmaril.Elgot.PartialWriter.Runs.iter_mapReturn

omit [CompleteLattice W] [ContinuousLog W] in
private theorem output_mapReturn_of_no_return (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A)
    (hn : ∀ b, Sum.inl b ∉ (f a).value) :
    (mapReturn f g a).output = (f a).output := by
  rcases _root_.Part.eq_none_or_eq_some (f a).value with hn' | ⟨s, hs⟩
  · simp [mapReturn, bind, hn']
  · cases s with
    | inl b => exact (hn b (_root_.Part.eq_some_iff.mp hs)).elim
    | inr a' => rw [mapReturn_inr f g (_root_.Part.eq_some_iff.mp hs)]; rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_mapReturn_of_no_return := Silmaril.Elgot.PartialWriter.output_mapReturn_of_no_return

omit [ContinuousLog W] in
private theorem iterOutput_mapReturn_of_no_return (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A)
    (hn : ∀ b, b ∉ (iter f a).value) :
    iterOutput (mapReturn f g) a = iterOutput f a := by
  have hstop : ∀ w z, Prefix f a w z → ∀ b, Sum.inl b ∉ (f z).value := by
    intro w z hp b hb
    exact hn b ((mem_value_iter_iff f a b).mpr ⟨_, hp.append_run (.done hb)⟩)
  apply le_antisymm
  · apply iterOutput_le
    intro w z hp
    have hp' := (Prefix.mapReturn_iff f g a z w).mp hp
    rw [output_mapReturn_of_no_return f g z (hstop w z hp')]
    exact le_iterOutput hp'
  · apply iterOutput_le
    intro w z hp
    have hp' := (Prefix.mapReturn_iff f g a z w).mpr hp
    have hle := le_iterOutput hp'
    rwa [output_mapReturn_of_no_return f g z (hstop w z hp)] at hle
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_mapReturn_of_no_return := Silmaril.Elgot.PartialWriter.iterOutput_mapReturn_of_no_return

private theorem naturality (f : A → PartialWriter W (B ⊕ A)) (g : B → PartialWriter W C) :
    (iter f >=> g) = iter (mapReturn f g) := by
  funext a
  rcases _root_.Part.eq_none_or_eq_some (iter f a).value with hn | ⟨b, hb⟩
  · apply ext
    · simp only [Bind.kleisliRight, value_bind, value_iter, value_mapReturn]
      exact congrFun (Part.naturality (fun a => (f a).value) (fun b => (g b).value)) a
    · change ((iter f a) >>= g).output = iterOutput (mapReturn f g) a
      rw [iterOutput_mapReturn_of_no_return f g a (fun b => by rw [hn]; exact _root_.Part.notMem_none b)]
      have heq : iter f a = diverge (iterOutput f a) := ext hn rfl
      rw [heq, bind_def, bind_diverge]
      rfl
  · rcases (mem_value_iter_iff f a b).mp (_root_.Part.eq_some_iff.mp hb) with ⟨w, hr⟩
    rw [hr.iter_mapReturn, Bind.kleisliRight, hr.iter_eq_done]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.naturality := Silmaril.Elgot.PartialWriter.naturality

end Silmaril.Elgot.PartialWriter
