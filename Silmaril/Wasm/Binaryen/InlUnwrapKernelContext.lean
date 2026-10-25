module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelFolding

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

/-- Structural source heads embed in Core's converse instruction closure. -/
theorem UI.to_core_reverse {i j : Instr} :
    UI R i j → InstrRel (fun x y => UIL R y x) j i
  | .flat i => .refl i
  | .block h => .block _ (.base h)
  | .loop h => .loop _ (.base h)
  | .if_ ht he => .if_ _ (.base ht) (.base he)
  | .tryTable h => .tryTable _ _ (.base h)

/-- Structural runtime heads use the recursively expanded body relation. -/
theorem KUA.to_core_reverse {a b : Admin} :
    KUA R a b → AdminRel (fun x y => UIL R y x) (WithCuts (fun x y => KUL R y x)) b a
  | .plain h => .plain h.to_core_reverse
  | .ref r => .refl (.ref r)
  | .callRef d => .refl (.callRefType d)
  | .retCallRef d => .refl (.returnCallRefType d)
  | .label hc hb => .label _ (.base hc) (.base (.inl hb))
  | .handler hb => .handler _ _ (.base (.inl hb))
  | .frame hb => .frame _ _ (.base (.inl hb))
  | .trap => .refl .trap

/-- Every actual step at a structural noncontext head, including calls,
is matched without any transformed-source typing requirement. -/
theorem KUA.noncontext_step_reverse
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    {s t : Store H} {f : Frame} {original bare : Admin}
    {originalRest bareRest : List Admin} {ambient : List Val} {sourceNext : Config H}
    (stores : StoreRel F s t) (head : KUA R original bare)
    (rest : KUL R originalRest bareRest) (nonvalue : bare.val? = none)
    (noncontext : ¬ bare.IsCtx)
    (selected : Step P noHost
      ⟨s, f, vals ambient ++ [bare] ++ bareRest⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [original] ++ originalRest⟩
      (rank (vals ambient ++ [bare] ++ bareRest)) := by
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  by_cases call : bare.IsCallRef
  · exact Closure.call_case hF (by intro _ _ _ _ _ _ impossible; exact impossible.elim)
      stores head.to_core_reverse call (.base (Or.inl rest)) selected
  · exact Closure.seq_case stores head.to_core_reverse nonvalue noncontext call
      (.base (Or.inl rest)) selected

/-- The exact selected step under a structural label uses only original-body
typing; all recursive cuts and related continuation bodies are retained. -/
theorem kernel_label_step_reverse
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {s t : Store H} {f : Frame} {n : Nat} {cont originalCont : List Instr}
    {original bare originalRest bareRest : List Admin} {ambient : List Val}
    {sourceNext : Config H}
    (stores : StoreRel F s t) (continuation : UIL R originalCont cont)
    (body : KUL R original bare) (rest : KUL R originalRest bareRest)
    (typed : ContextTyped ⟨t, f, original⟩)
    (inside : ∀ {next : Config H}, Step P noHost ⟨s, f, bare⟩ next →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        next ⟨t, f, original⟩ (rank bare))
    (selected : Step P noHost
      ⟨s, f, vals ambient ++ [.label n cont bare] ++ bareRest⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [.label n originalCont original] ++ originalRest⟩
      (rank (vals ambient ++ [.label n cont bare] ++ bareRest)) := by
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  exact Closure.kernel_label_case_of_body hF
    (by intro _ _ _ _ _ _ impossible; exact impossible.elim)
    (typed_kernel_expanded_facts_reverse budget labels F) inside stores (.base continuation)
    (.base (Or.inl body)) (.base (Or.inl rest)) typed selected

theorem kernel_handler_step_reverse
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {s t : Store H} {f : Frame} {n : Nat} {catches : List Catch}
    {original bare originalRest bareRest : List Admin} {ambient : List Val}
    {sourceNext : Config H}
    (stores : StoreRel F s t) (body : KUL R original bare)
    (rest : KUL R originalRest bareRest) (typed : ContextTyped ⟨t, f, original⟩)
    (inside : ∀ {next : Config H}, Step P noHost ⟨s, f, bare⟩ next →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        next ⟨t, f, original⟩ (rank bare))
    (selected : Step P noHost
      ⟨s, f, vals ambient ++ [.handler n catches bare] ++ bareRest⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [.handler n catches original] ++ originalRest⟩
      (rank (vals ambient ++ [.handler n catches bare] ++ bareRest)) := by
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  exact Closure.kernel_handler_case_of_body hF
    (by intro _ _ _ _ _ _ impossible; exact impossible.elim)
    (typed_kernel_expanded_facts_reverse budget labels F) inside stores
    (.base (Or.inl body)) (.base (Or.inl rest)) typed selected

theorem kernel_frame_step_reverse
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {s t : Store H} {f innerFrame : Frame} {n : Nat}
    {original bare originalRest bareRest : List Admin} {ambient : List Val}
    {sourceNext : Config H}
    (stores : StoreRel F s t) (body : KUL R original bare)
    (rest : KUL R originalRest bareRest) (typed : ContextTyped ⟨t, innerFrame, original⟩)
    (inside : ∀ {next : Config H}, Step P noHost ⟨s, innerFrame, bare⟩ next →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        next ⟨t, innerFrame, original⟩ (rank bare))
    (selected : Step P noHost
      ⟨s, f, vals ambient ++ [.frame n innerFrame bare] ++ bareRest⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [.frame n innerFrame original] ++ originalRest⟩
      (rank (vals ambient ++ [.frame n innerFrame bare] ++ bareRest)) := by
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  exact Closure.kernel_frame_case_of_body hF
    (by intro _ _ _ _ _ _ impossible; exact impossible.elim)
    (typed_kernel_expanded_facts_reverse budget labels F) inside stores
    (.base (Or.inl body)) (.base (Or.inl rest)) typed selected

end Silmaril.Wasm.Binaryen.Unwrap
