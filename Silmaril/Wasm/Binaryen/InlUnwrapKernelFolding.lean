module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelRunning

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

/-- Match an actual inner reduction of a folded runtime label. The original
common tail remains inside its wrapper while the transformed tail stays outside.
The ready-values phase and arbitrary nested cuts are retained in `KUL`. -/
theorem folded_body_step_match
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame} {n : Nat}
    {original bare common originalRest bareRest : List Admin} {ambient : List Val}
    {sourceNext : Config H}
    (safe : NoEsc (original ++ common)) (rest : KUL R originalRest bareRest)
    (selected : Step P noHost ⟨s, f, bare⟩ sourceNext)
    (inside : RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, original⟩ (rank bare)) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨sourceNext.store, sourceNext.frame,
        vals ambient ++ [.label n [] sourceNext.code] ++ (common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩
      (rank (vals ambient ++ [.label n [] bare] ++ (common ++ bareRest))) := by
  obtain ⟨sourceStore, sourceFrame, sourceCode⟩ := sourceNext
  obtain ⟨⟨targetStore, targetFrame, targetCode⟩, progress, stores, frames, related⟩ := inside
  dsimp only at progress stores frames related ⊢
  subst targetFrame
  have body : KUL R targetCode sourceCode := KUL.of_core_reverse related
  rcases progress with progress | ⟨same, decrease⟩
  · have run := Closure.transGen_append_right progress common
    have guarded : NoEsc (targetCode ++ common) := safe.steps run.to_reflTransGen
    refine ⟨⟨targetStore, sourceFrame,
      vals ambient ++ [.label n [] (targetCode ++ common)] ++ originalRest⟩,
      Or.inl ?_, stores, rfl, .base (Or.inl ?_)⟩
    · exact Closure.transGen_ctx (Closure.transGen_label run n []) ambient originalRest
    · simpa only [List.append_assoc, List.singleton_append] using
        (KUL.refl (vals ambient)).append (KUL.foldLabel body guarded rest)
  · cases same
    refine ⟨⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩,
      Or.inr ⟨rfl, ?_⟩, stores, rfl, .base (Or.inl ?_)⟩
    · exact LawfulCodeRank.label_lt (vals ambient) (common ++ bareRest) n [] decrease
    · simpa only [List.append_assoc, List.singleton_append] using
        (KUL.refl (vals ambient)).append (KUL.foldLabel body safe rest)

/-- Completing a values-ready transformed label enters the original's running
unwrap phase. A nonempty original normalization trace is optional: removing the
source label already decreases the lawful contextual rank. -/
theorem folded_values_match
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame} {n : Nat}
    {original common originalRest bareRest : List Admin} {ambient values : List Val}
    (stores : StoreRel F s t) (body : KUL R original (vals values))
    (safe : NoEsc (original ++ common)) (rest : KUL R originalRest bareRest)
    (typed : ContextTyped
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨s, f, vals ambient ++ vals values ++ (common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩
      (rank (vals ambient ++ [.label n [] (vals values)] ++ (common ++ bareRest))) := by
  have typedBody : ContextTyped ⟨t, f, original⟩ :=
    ContextTyped.suffix (ContextTyped.label typed)
  have normalize : Steps P noHost ⟨t, f, original⟩ ⟨t, f, vals values⟩ := by
    simpa only [Execution.Core.vals_nil', List.nil_append] using
      KUL.typed_values_reverse (P := P) body (vs := []) (by simpa using typedBody) rfl
  have run := Steps.append_right normalize common
  have guarded : NoEsc (vals values ++ common) := safe.steps run
  have outer := Steps.append_right (Steps.vals_left (Closure.steps_label run n []) ambient) originalRest
  refine Matched.of_steps outer ?_
  refine ⟨⟨t, f, vals ambient ++ [.label n [] (vals values ++ common)] ++ originalRest⟩,
    Or.inr ⟨rfl, ?_⟩, stores, rfl, .base (Or.inl ?_)⟩
  · have smaller : rank (vals values) < rank [.label n [] (vals values)] := by
      simpa using LawfulCodeRank.label_body_lt (rank := rank) [] [] n [] (vals values)
    simpa only [List.append_assoc] using
      LawfulCodeRank.context_lt (vals ambient) (common ++ bareRest) smaller
  · simpa only [List.append_assoc, List.singleton_append] using
      (KUL.refl (vals ambient)).append
        (KUL.run (KUL.refl (vals values ++ common)) guarded rest)

omit [LawfulCodeRank rank] in
/-- A kernel exits the original folded label after its actual normalization,
including the original common tail. The transformed outside tail is then an
unobservable kernel-cut suffix. -/
theorem folded_kernel_match
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame} {n : Nat}
    {original common originalRest bareRest k : List Admin} {ambient : List Val}
    (stores : StoreRel F s t) (body : KUL R original k)
    (typed : ContextTyped
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩)
    (kernel : k = [.trap] ∨ ∃ a, k = throwing a) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨s, f, vals ambient ++ k ++ (common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩
      (rank (vals ambient ++ [.label n [] k] ++ (common ++ bareRest))) := by
  have typedBody : ContextTyped ⟨t, f, original⟩ :=
    ContextTyped.suffix (ContextTyped.label typed)
  have normalize : Steps P noHost ⟨t, f, original⟩ ⟨t, f, k⟩ := by
    simpa only [Execution.Core.vals_nil', List.nil_append] using
      KUL.typed_kernel_exit_reverse (P := P) body (vs := []) (us := []) (rest := [])
        (by simpa using typedBody) kernel (by simp)
  have inside := (Steps.append_right normalize common).trans
    (Closure.steps_kernel kernel [] common)
  have leave : Step P noHost ⟨t, f, [.label n [] k]⟩ ⟨t, f, k⟩ := by
    rcases kernel with rfl | ⟨a, rfl⟩
    exacts [Step.trapLabel, Step.throwRefLabel]
  have progress : Relation.TransGen (Step P noHost)
      ⟨t, f, [.label n [] (original ++ common)]⟩ ⟨t, f, k⟩ :=
    Relation.TransGen.tail' (Closure.steps_label inside n []) leave
  refine ⟨⟨t, f, vals ambient ++ k ++ originalRest⟩,
    Or.inl (Closure.transGen_ctx progress ambient originalRest), stores, rfl, .base (Or.inr ?_)⟩
  exact ⟨ambient, ambient, k, common ++ bareRest, originalRest, kernel, rfl, rfl⟩

/-- Real original escape freedom rules out a transformed blocked exit even
when earlier matching introduced cuts in the recursively related body. -/
theorem KUL.no_blocked_of_guard
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {s : Store H} {f : Frame} {original bare suffix : List Admin}
    {values : List Val} {e : Admin} {rest : List Admin}
    (body : KUL R original bare) (safe : NoEsc (original ++ suffix))
    (typed : ContextTyped ⟨s, f, original⟩)
    (shape : bare = vals values ++ e :: rest) (he : e.val? = none) (blocked : Blocked e) :
    False := by
  obtain ⟨tail, run⟩ := KUL.typed_blocked_exit_reverse (P := .spec true)
    budget labels body (vs := []) (by simpa using typed) shape he blocked
  have guarded := safe.steps (Steps.append_right run suffix)
  rcases blocked with ⟨l, rfl⟩ | rfl | call
  · exact guarded.no_br (l := l) (vs := values) (rest := tail ++ suffix) (by simp)
  · exact guarded.no_return (vs := values) (rest := tail ++ suffix) (by simp)
  · exact guarded.no_retCall call (vs := values) (rest := tail ++ suffix) (by simp)

end Silmaril.Wasm.Binaryen.Unwrap
