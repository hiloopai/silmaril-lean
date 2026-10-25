module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelOperandBoundary

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

/-- Every selected step whose active code is already a trap/exception
kernel is matched by normalization and a rank-decreasing kernel cut. -/
theorem KUL.kernel_step_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {original bare : List Admin} {ambient us : List Val} {k rest : List Admin}
    {sourceNext : Config H}
    (stores : StoreRel F s t) (related : KUL R original bare)
    (typed : ContextTyped ⟨t, f, vals ambient ++ original⟩)
    (kernel : k = [.trap] ∨ ∃ a, k = throwing a)
    (shape : vals ambient ++ bare = vals us ++ k ++ rest)
    (selected : Step P noHost ⟨s, f, vals ambient ++ bare⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ original⟩ (rank (vals ambient ++ bare)) := by
  have normalize := KUL.typed_kernel_exit_reverse (P := P) related typed kernel shape
  refine Matched.of_steps normalize ?_
  exact Closure.cut_case kernel stores (U := us) (X := rest) (W := []) (Y := [])
    shape (by simp) selected

/-- All administrative bubbling steps are covered, including partial prefix
and suffix discard. The selected source reduction and profile remain exact. -/
theorem KUL.bubble_step_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {original bare : List Admin} {ambient : List Val} {sourceNext : Config H}
    (stores : StoreRel F s t) (related : KUL R original bare)
    (typed : ContextTyped ⟨t, f, vals ambient ++ original⟩)
    (bubble : Bubble s f (vals ambient ++ bare) sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ original⟩ (rank (vals ambient ++ bare)) := by
  obtain ⟨pre, discarded, k, left, right, shape, kernel, nonempty, result⟩ := bubble
  apply KUL.kernel_step_reverse stores related typed kernel shape
  exact Bubble.toStep ⟨pre, discarded, k, left, right, shape, kernel, nonempty, result⟩

/-- Lift the actual selected computational head through an original-only
running wrapper. The inner callback may return recursively nested kernel cuts,
related callee code and a changed frame; no transformed typing is assumed. -/
theorem running_head_match
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    {s t : Store H} {f : Frame} {n : Nat}
    {original bare originalRest bareRest : List Admin}
    {ambient inner outer args : List Val} {e : Admin} {tail : List Admin} {next : Config H}
    (stores : StoreRel F s t) (body : KUL R original bare) (safe : NoEsc original)
    (rest : KUL R originalRest bareRest)
    (typed : ContextTyped ⟨t, f, vals ambient ++ [.label n [] original] ++ originalRest⟩)
    (shape : bare = vals inner ++ e :: tail) (he : e.val? = none)
    (head : Head P s f args e next) (operands : ambient ++ inner = outer ++ args)
    (inside : ∀ {sourceNext : Config H}, Step P noHost ⟨s, f, bare⟩ sourceNext →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        sourceNext ⟨t, f, original⟩ (rank bare)) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨next.store, next.frame, vals outer ++ next.code ++ (tail ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.label n [] original] ++ originalRest⟩
      (rank (vals ambient ++ bare ++ bareRest)) := by
  have typedBody : ContextTyped ⟨t, f, original⟩ := ContextTyped.label typed
  obtain ⟨sourceNext, selected, after⟩ := KUL.cancel_head_active hF stores body
    (vs := []) (pre := ambient) (suffix := bareRest) (by simpa using typedBody)
    shape he head (by simpa using operands)
  have selected' : Step P noHost ⟨s, f, bare⟩ sourceNext := by
    simpa only [shape, Execution.Core.vals_nil', List.nil_append] using selected
  rw [after]
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  obtain ⟨⟨targetStore, targetFrame, targetCode⟩, progress, relatedStore, frames, relatedCode⟩ :=
    inside selected'
  dsimp only at progress relatedStore frames relatedCode ⊢
  subst targetFrame
  have matchedBody : KUL R targetCode sourceCode := KUL.of_core_reverse relatedCode
  rcases progress with progress | ⟨same, decrease⟩
  · have guarded : NoEsc targetCode := safe.steps progress.to_reflTransGen
    refine ⟨⟨targetStore, sourceFrame,
      vals ambient ++ [.label n [] targetCode] ++ originalRest⟩, Or.inl ?_,
      relatedStore, rfl, .base (Or.inl ?_)⟩
    · exact Closure.transGen_ctx (Closure.transGen_label progress n []) ambient originalRest
    · simpa only [List.append_assoc, List.singleton_append] using
        (KUL.refl (vals ambient)).append (KUL.run matchedBody guarded rest)
  · cases same
    refine ⟨⟨t, f, vals ambient ++ [.label n [] original] ++ originalRest⟩,
      Or.inr ⟨rfl, ?_⟩, relatedStore, rfl, .base (Or.inl ?_)⟩
    · exact LawfulCodeRank.context_lt (vals ambient) bareRest decrease
    · simpa only [List.append_assoc, List.singleton_append] using
        (KUL.refl (vals ambient)).append (KUL.run matchedBody safe rest)

end Silmaril.Wasm.Binaryen.Unwrap
