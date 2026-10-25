module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelContext

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}

/-- Enter an original unwrap site and match the actual chosen computational
head of its bare region. This includes null `throw_ref`, preserves changed
callees, and borrows no values from outside the real block signature. -/
theorem kernel_site_head_reverse
    {rank : List Admin → Nat} {m : Nat}
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    {s t : Store H} {f : Frame} {bt : BlockType}
    {originalRest bareRest : List Admin}
    {ambient inner outer operands : List Val} {e : Admin} {tail : List Admin}
    {next : Config H}
    (stores : StoreRel F s t) (rest : KUL R originalRest bareRest)
    (safe : NoEsc (expression R))
    (typed : ContextTyped ⟨t, f, vals ambient ++ [.plain (.block bt R)] ++ originalRest⟩)
    (shape : expression R = vals inner ++ e :: tail) (he : e.val? = none)
    (head : Head P s f operands e next) (split : ambient ++ inner = outer ++ operands) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨next.store, next.frame, vals outer ++ next.code ++ (tail ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.plain (.block bt R)] ++ originalRest⟩ m := by
  obtain ⟨pre, params, ps, rs, ambientEq, resolved, arity⟩ := ContextTyped.block_ready typed
  have entry : Step P noHost
      ⟨t, f, vals ambient ++ [.plain (.block bt R)] ++ originalRest⟩
      ⟨t, f, vals pre ++ [.label rs.length [] (vals params ++ expression R)] ++ originalRest⟩ := by
    simpa only [ambientEq, vals_append, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.block resolved arity) pre) originalRest
  have typedBody : ContextTyped ⟨t, f, vals params ++ expression R⟩ :=
    ContextTyped.label (typed.step entry)
  obtain ⟨sourceNext, selected, after⟩ := KUL.cancel_head_active hF stores (KUL.refl (R := R) (expression R))
    (vs := params) (pre := pre) (suffix := bareRest) typedBody shape he head
    (by simpa only [ambientEq, List.append_assoc] using split)
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  have sourceStep : Step P noHost
      ⟨s, f, vals params ++ expression R⟩ ⟨sourceStore, sourceFrame, sourceCode⟩ := by
    simpa only [shape, vals_append, List.append_assoc] using selected
  obtain ⟨targetStore, targetCode, targetStep, relatedStores, relatedCode⟩ :=
    Step.match_storeRel (B := fun x y => UL R y x) hF
      (by intro _ _ _ _ _ _ impossible; exact impossible.elim) sourceStep t stores
  have running : KUL R targetCode sourceCode := (UL.of_core_reverse relatedCode).to_kernel
  have guarded : NoEsc targetCode := (safe.vals_left params).step targetStep
  rw [after]
  refine ⟨⟨targetStore, sourceFrame,
    vals pre ++ [.label rs.length [] targetCode] ++ originalRest⟩,
    Or.inl ?_, relatedStores, rfl, .base (Or.inl ?_)⟩
  · exact (Relation.TransGen.single entry).tail
      (Step.append_right (Step.vals_left (Step.ctxtLabel targetStep) pre) originalRest)
  · simpa only [List.append_assoc, List.singleton_append] using
      (KUL.refl (vals pre)).append (KUL.run running guarded rest)

end Silmaril.Wasm.Binaryen.Unwrap
