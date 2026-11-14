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
# Flattening nested partial-writer iteration: proofs

Proofs for `Silmaril.Semantics.TraceModels.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.
-/

public section

namespace Silmaril.Elgot.PartialWriter

universe u

variable {W A B : Type u} [Monoid W]

@[simp] private theorem value_flattenBody (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    (flattenBody f a).value = flattenBody (fun a => (f a).value) a := rfl
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.value_flattenBody := Silmaril.Elgot.PartialWriter.value_flattenBody

@[simp] private theorem output_flattenBody (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    (flattenBody f a).output = (f a).output := by
  change (f a >>= pure ∘ flatten).output = (f a).output
  induction f a using cases_on with
  | hdiverge w => rw [bind_def, bind_diverge]; rfl
  | hdone s w => rw [bind_def, bind_done]; exact mul_one w
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.output_flattenBody := Silmaril.Elgot.PartialWriter.output_flattenBody

private theorem mem_flattenBody_continue (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a a' : A) :
    Sum.inr a' ∈ (flattenBody f a).value ↔
      Sum.inl (Sum.inr a') ∈ (f a).value ∨ Sum.inr a' ∈ (f a).value := by
  rw [value_flattenBody, Part.mem_flattenBody_iff]
  constructor
  · rintro ⟨s, hs, heq⟩
    cases s with
    | inl s =>
        cases s with
        | inl b => cases heq
        | inr c => cases heq; exact .inl hs
    | inr c => cases heq; exact .inr hs
  · rintro (hs | hs)
    · exact ⟨_, hs, rfl⟩
    · exact ⟨_, hs, rfl⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.mem_flattenBody_continue := Silmaril.Elgot.PartialWriter.mem_flattenBody_continue

private theorem Prefix.snoc {f : A → PartialWriter W (B ⊕ A)} {a z z' : A} {w : W}
    (h : Prefix f a w z) (hs : Sum.inr z' ∈ (f z).value) :
    Prefix f a (w * (f z).output) z' := by
  simpa only [mul_one] using h.append (Prefix.step hs (Prefix.start z'))
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.snoc := Silmaril.Elgot.PartialWriter.Prefix.snoc

private theorem Prefix.flatten {f : A → PartialWriter W ((B ⊕ A) ⊕ A)} {a z : A} {w : W}
    (h : Prefix f a w z) : Prefix (flattenBody f) a w z := by
  induction h with
  | start a => exact .start a
  | step hs _ ih =>
      simpa only [output_flattenBody] using
        Prefix.step ((mem_flattenBody_continue f _ _).2 (.inr hs)) ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten := Silmaril.Elgot.PartialWriter.Prefix.flatten

private theorem Runs.flatten_continue {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a a' : A} {w : W} (h : Runs f a w (.inr a')) :
    Prefix (flattenBody f) a w a' := by
  generalize heq : (Sum.inr a' : B ⊕ A) = s at h
  induction h with
  | done hs =>
      cases heq
      simpa only [output_flattenBody, mul_one] using
        Prefix.step ((mem_flattenBody_continue f _ _).2 (.inl hs)) (Prefix.start _)
  | step hs _ ih =>
      simpa only [output_flattenBody] using
        Prefix.step ((mem_flattenBody_continue f _ _).2 (.inr hs)) (ih heq)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Runs.flatten_continue := Silmaril.Elgot.PartialWriter.Runs.flatten_continue

variable [CompleteLattice W] [ContinuousLog W]

private theorem Prefix.iter_flatten {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (iter f) a w z) :
    Prefix (flattenBody f) a w z := by
  induction h with
  | start a => exact .start a
  | step hs _ ih =>
      obtain ⟨v, hv⟩ := (mem_value_iter_iff f _ _).1 hs
      have hout := congrArg PartialWriter.output hv.iter_eq_done
      simpa only [done] using hout ▸ hv.flatten_continue.append ih
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.iter_flatten := Silmaril.Elgot.PartialWriter.Prefix.iter_flatten

private theorem Prefix.flatten_decompose_aux {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (flattenBody f) a w z) :
    ∀ {start c : A} {u v : W}, Prefix (iter f) start u c → Prefix f c v a →
      ∃ c' u' v', Prefix (iter f) start u' c' ∧ Prefix f c' v' z ∧ u' * v' = u * v * w := by
  induction h with
  | start a =>
      intro start c u v ho hi
      exact ⟨c, u, v, ho, hi, by rw [mul_one]⟩
  | @step a a' z w hs _ ih =>
      intro start c u v ho hi
      rcases (mem_flattenBody_continue f a a').1 hs with hb | hr
      · have hrun := hi.append_run (Runs.done hb)
        have hiter := hrun.iter_eq_done
        have hnext : Sum.inr a' ∈ (iter f c).value := by
          rw [hiter]
          exact _root_.Part.mem_some _
        have hout : (iter f c).output = v * (f a).output := congrArg PartialWriter.output hiter
        obtain ⟨c', u', v', ho', hi', heq⟩ := ih (ho.snoc hnext) (Prefix.start a')
        exact ⟨c', u', v', ho', hi', by
          simpa only [hout, one_mul, mul_one, output_flattenBody, mul_assoc] using heq⟩
      · obtain ⟨c', u', v', ho', hi', heq⟩ := ih ho (hi.snoc hr)
        exact ⟨c', u', v', ho', hi', by
          simpa only [output_flattenBody, mul_assoc] using heq⟩
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten_decompose_aux := Silmaril.Elgot.PartialWriter.Prefix.flatten_decompose_aux

private theorem Prefix.flatten_decompose {f : A → PartialWriter W ((B ⊕ A) ⊕ A)}
    {a z : A} {w : W} (h : Prefix (flattenBody f) a w z) :
    ∃ c u v, Prefix (iter f) a u c ∧ Prefix f c v z ∧ u * v = w := by
  simpa only [one_mul] using h.flatten_decompose_aux (Prefix.start a) (Prefix.start a)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.Prefix.flatten_decompose := Silmaril.Elgot.PartialWriter.Prefix.flatten_decompose

private theorem iterOutput_codiagonal (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) (a : A) :
    iterOutput (iter f) a = iterOutput (flattenBody f) a := by
  apply le_antisymm
  · apply iterOutput_le
    intro u c ho
    rw [output_iter, iterOutput, ContinuousLog.mul_sSup _ _ (observations_nonempty f c)]
    apply sSup_le
    rintro _ ⟨_, ⟨v, z, hi, rfl⟩, rfl⟩
    simpa only [output_flattenBody, mul_assoc] using
      le_iterOutput (ho.iter_flatten.append hi.flatten)
  · apply iterOutput_le
    intro w z h
    obtain ⟨c, u, v, ho, hi, heq⟩ := h.flatten_decompose
    rw [output_flattenBody, ← heq, mul_assoc]
    exact (ContinuousLog.mul_mono (le_refl u) (le_iterOutput hi)).trans (le_iterOutput ho)
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.iterOutput_codiagonal := Silmaril.Elgot.PartialWriter.iterOutput_codiagonal

private theorem codiagonal (f : A → PartialWriter W ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply ext
  · simp only [value_iter, value_flattenBody]
    exact congrFun (LawfulElgotMonad.codiagonal (fun a => (f a).value)) a
  · exact iterOutput_codiagonal f a
alias _root_.Silmaril.Proofs.Semantics.Elgot.PartialWriter.codiagonal := Silmaril.Elgot.PartialWriter.codiagonal

end Silmaril.Elgot.PartialWriter
