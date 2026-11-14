module

public import Silmaril.Semantics.TraceModels.Defs
public import Silmaril.Proofs.Semantics.TraceModels.OrderedLog
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
public import Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import all Silmaril.Proofs.Semantics.TraceModels.OrderedLog
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Traces
import all Silmaril.Proofs.Semantics.TraceModels.PartialWriter.Iteration
import Batteries.Tactic.Alias

/-!
# PartialWriter.Algebra: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B C : Type u} [Monoid W]

@[simp] private theorem value_map (f : A → B) (x : PartialWriter W A) :
    (f <$> x).value = f <$> x.value := by
  simp only [← bind_pure_comp, value_bind, value_pure]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_map := Silmaril.Elgot.PartialWriter.value_map

@[simp] private theorem output_map (f : A → B) (x : PartialWriter W A) :
    (f <$> x).output = x.output := by
  induction x using cases_on with
  | hdiverge w => simp only [← bind_pure_comp, bind_def, bind_diverge]; rfl
  | hdone a w => simp only [← bind_pure_comp, bind_def, bind_done, output_pure, mul_one]; rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_map := Silmaril.Elgot.PartialWriter.output_map

private theorem value_mapReturn (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a : A) :
    (mapReturn f g a).value =
      mapReturn (fun a => (f a).value) (fun b => (g b).value) a := by
  simp only [mapReturn, value_bind]
  apply bind_congr
  intro s
  cases s <;> rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_mapReturn := Silmaril.Elgot.PartialWriter.value_mapReturn

private theorem mapReturn_inr (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) {a a' : A} (h : Sum.inr a' ∈ (f a).value) :
    mapReturn f g a = done (Sum.inr a') (f a).output := by
  have hf : f a = done (.inr a') (f a).output := ext (_root_.Part.eq_some_iff.mpr h) rfl
  unfold mapReturn
  rw [hf, bind_def, bind_done]
  simp [done]
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.mapReturn_inr := Silmaril.Elgot.PartialWriter.mapReturn_inr

private theorem mem_mapReturn_inr_iff (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a a' : A) :
    Sum.inr a' ∈ (mapReturn f g a).value ↔ Sum.inr a' ∈ (f a).value := by
  rw [value_mapReturn, Part.mem_mapReturn_iff]
  simp
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_mapReturn_inr_iff := Silmaril.Elgot.PartialWriter.mem_mapReturn_inr_iff

private theorem Prefix.mapReturn_iff (f : A → PartialWriter W (B ⊕ A))
    (g : B → PartialWriter W C) (a z : A) (w : W) :
    Prefix (mapReturn f g) a w z ↔ Prefix f a w z := by
  constructor
  · intro h
    induction h with
    | start a => exact .start a
    | step hs _ ih =>
        have hs' := (mem_mapReturn_inr_iff f g _ _).mp hs
        simpa only [mapReturn_inr f g hs', done] using Prefix.step hs' ih
  · intro h
    induction h with
    | start a => exact .start a
    | step hs _ ih =>
        have hs' := (mem_mapReturn_inr_iff f g _ _).mpr hs
        simpa only [mapReturn_inr f g hs, done] using Prefix.step hs' ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.mapReturn_iff := Silmaril.Elgot.PartialWriter.Prefix.mapReturn_iff

end Silmaril.Elgot.PartialWriter
