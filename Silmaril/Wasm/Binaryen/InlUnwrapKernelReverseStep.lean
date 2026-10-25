module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelSelected

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]
variable {F : FuncInst H → FuncInst H → Prop}

mutual
/-- Full arbitrary-profile reverse matching for the recursively kernel-expanded
unwrap/folding relation. Only the original target supplies typing. -/
theorem KUL.typed_step_reverse
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {original bare : List Admin} (related : KUL R original bare)
    {s t : Store H} {f : Frame} {ambient : List Val} {sourceNext : Config H}
    (stores : StoreRel F s t) (typed : ContextTyped ⟨t, f, vals ambient ++ original⟩)
    (selected : Step P noHost ⟨s, f, vals ambient ++ bare⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ original⟩ (rank (vals ambient ++ bare)) := by
  cases related with
  | nil => exact (by simpa using selected.not_all_isVal : False).elim
  | @cons a b originalRest bareRest head rest =>
    cases value : b.val? with
    | none =>
      simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using KUA.typed_step_reverse hF budget labels head rest
        stores (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed) value
        (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using selected)
    | some v =>
      obtain rfl := Admin.eq_of_val? value
      obtain rfl := KUA.eq_of_val_right head
      have typedTail : ContextTyped ⟨t, f, vals (ambient ++ [v]) ++ originalRest⟩ := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed
      have selectedTail : Step P noHost
          ⟨s, f, vals (ambient ++ [v]) ++ bareRest⟩ sourceNext := by
        simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using selected
      simpa only [vals_append, vals_cons', Execution.Core.vals_nil', List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using
        KUL.typed_step_reverse hF budget labels rest stores typedTail selectedTail
  | @site bt originalRest bareRest rest =>
    rcases Step.decomp selected with computational | bubble
    swap
    · exact KUL.bubble_step_reverse stores (.site bt rest) typed bubble
    by_cases all : (expression R).all Admin.isVal = true
    · obtain ⟨values, valuesEq⟩ := exists_vals_of_all all
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (site_values_continue_reverse (R := R) (rank := rank)
          (m := rank (vals ambient ++ (expression R ++ bareRest)))
          (originalRest := originalRest) (bareRest := bareRest) (ambient := ambient)
          (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using typed) valuesEq
          (by simpa only [List.append_assoc] using selected) (fun normalized actual => by
            simpa only [valuesEq, vals_append, List.append_assoc] using
              KUL.typed_step_reverse hF budget labels rest stores normalized actual))
    · have active : (expression R).all Admin.isVal = false := Bool.eq_false_iff.mpr all
      obtain ⟨inner, e, tail, he, shape⟩ := exists_head_of_not_all active
      obtain ⟨outer, args, result, split, head, after⟩ := selected_head_at_first
        (values := ambient ++ inner) (e := e) (tail := tail ++ bareRest)
        (by simp only [shape, vals_append, List.append_assoc, List.cons_append]) he computational
      subst sourceNext
      simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, List.append_assoc] using kernel_site_head_reverse
        (rank := rank) (m := rank (vals ambient ++ (expression R ++ bareRest)))
        hF stores rest (by simpa using noEsc_fold (show FoldOk R from ⟨budget, labels⟩) [])
        (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed) shape he head split
  | @run n originalBody bareBody originalRest bareRest body safe rest =>
    rcases Step.decomp selected with computational | bubble
    swap
    · exact KUL.bubble_step_reverse stores (.run body safe rest) typed bubble
    by_cases all : bareBody.all Admin.isVal = true
    · obtain ⟨values, valuesEq⟩ := exists_vals_of_all all
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (running_values_continue_reverse (rank := rank)
          (m := rank (vals ambient ++ (bareBody ++ bareRest)))
          (originalRest := originalRest) (bareRest := bareRest) (ambient := ambient)
          body safe (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using typed) valuesEq
          (by simpa only [List.append_assoc] using selected) (fun normalized actual => by
            simpa only [valuesEq, vals_append, List.append_assoc] using
              KUL.typed_step_reverse hF budget labels rest stores normalized actual))
    · have active : bareBody.all Admin.isVal = false := Bool.eq_false_iff.mpr all
      obtain ⟨inner, e, tail, he, shape⟩ := exists_head_of_not_all active
      obtain ⟨outer, args, result, split, head, after⟩ := selected_head_at_first
        (values := ambient ++ inner) (e := e) (tail := tail ++ bareRest)
        (by simp only [shape, vals_append, List.append_assoc, List.cons_append]) he computational
      subst sourceNext
      simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc, List.append_assoc] using running_head_match hF stores
        body safe rest (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed) shape he head split
        (fun actual => by
          have bodyTyped : ContextTyped ⟨t, f, originalBody⟩ := ContextTyped.label
            (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed)
          simpa only [Execution.Core.vals_nil', List.nil_append] using
            KUL.typed_step_reverse hF budget labels body (ambient := []) stores
              (by simpa using bodyTyped) (by simpa using actual))
  | @foldIf bt yes yes' no no' common originalRest bareRest yesRel noRel yesSafe noSafe rest =>
    rcases Step.decomp selected with computational | bubble
    swap
    · exact KUL.bubble_step_reverse stores (.foldIf bt yesRel noRel yesSafe noSafe rest) typed bubble
    obtain ⟨outer, args, result, split, head, after⟩ := selected_head_at_first
      (values := ambient) (e := .plain (.if_ bt yes' no'))
      (tail := expression common ++ bareRest) rfl rfl computational
    subst sourceNext
    cases head with
    | ifTrue condition =>
      simpa [split, vals_append, vals, Val.toAdmin, Val.i32, IntType.width, constI32, List.append_assoc] using
        fold_if_true_reverse (rank := rank)
          (m := rank (vals ambient ++ (.plain (.if_ bt yes' no') :: (expression common ++ bareRest))))
          stores yesRel yesSafe rest condition
    | ifFalse condition =>
      simpa [split, vals_append, vals, Val.toAdmin, Val.i32, IntType.width, constI32, List.append_assoc] using
        fold_if_false_reverse (rank := rank)
          (m := rank (vals ambient ++ (.plain (.if_ bt yes' no') :: (expression common ++ bareRest))))
          stores noRel noSafe rest condition
    | callRefNull call => exact call.elim
    | callRefFunc _ call => exact call.elim
    | parametric _ => fam_dismiss
    | numeric _ => fam_dismiss
    | vector _ => fam_dismiss
    | «variable» _ => fam_dismiss
    | table _ => fam_dismiss
    | memory _ => fam_dismiss
    | reference _ => fam_dismiss
    | aggregate _ => fam_dismiss
  | @foldBlock bt originalBody bareBody common originalRest bareRest body safe rest =>
    rcases Step.decomp selected with computational | bubble
    swap
    · exact KUL.bubble_step_reverse stores (.foldBlock bt body safe rest) typed bubble
    obtain ⟨outer, args, result, split, head, after⟩ := selected_head_at_first
      (values := ambient) (e := .plain (.block bt bareBody))
      (tail := expression common ++ bareRest) rfl rfl computational
    subst sourceNext
    cases head with
    | block resolved arity =>
      simpa only [split, vals_append, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using
        fold_block_reverse (rank := rank)
          (m := rank (vals ambient ++ (.plain (.block bt bareBody) :: (expression common ++ bareRest))))
          stores body safe rest resolved arity
    | callRefNull call => exact call.elim
    | callRefFunc _ call => exact call.elim
    | parametric _ => fam_dismiss
    | numeric _ => fam_dismiss
    | vector _ => fam_dismiss
    | «variable» _ => fam_dismiss
    | table _ => fam_dismiss
    | memory _ => fam_dismiss
    | reference _ => fam_dismiss
    | aggregate _ => fam_dismiss
  | @foldLabel n originalBody bareBody common originalRest bareRest body safe rest =>
    rcases Step.decomp selected with computational | bubble
    swap
    · exact KUL.bubble_step_reverse stores (.foldLabel body safe rest) typed bubble
    obtain ⟨outer, args, result, split, head, after⟩ := selected_head_at_first
      (values := ambient) (e := .label n [] bareBody)
      (tail := common ++ bareRest) rfl rfl computational
    subst sourceNext
    simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using folded_label_head_reverse budget labels stores body safe rest
      (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed)
      (fun actual => by
        have bodyTyped : ContextTyped ⟨t, f, originalBody⟩ :=
          ContextTyped.suffix (ContextTyped.label
            (by simpa only [List.singleton_append, List.cons_append, List.nil_append, List.append_assoc] using typed))
        simpa only [Execution.Core.vals_nil', List.nil_append] using
          KUL.typed_step_reverse hF budget labels body (ambient := []) stores
            (by simpa using bodyTyped) (by simpa using actual)) head split
  | @foldExit n values k junk originalRest bareRest kernel rest =>
    exact KUL.kernel_step_reverse stores (.foldExit kernel rest) typed kernel
      (us := ambient) (rest := bareRest) (by simp) selected
  | cut discard =>
    have cutRelation : KUL R original bare := .cut discard
    obtain ⟨us, ws, k, bareTail, originalTail, kernel, bareEq, originalEq⟩ := discard
    exact KUL.kernel_step_reverse stores cutRelation typed kernel
      (us := ambient ++ us) (rest := bareTail) (by simp [bareEq]) selected
termination_by sizeOf original
decreasing_by
  all_goals subst original
  all_goals simp_wf
  all_goals try have := sizeOf_append_left originalBody common
  all_goals omega

/-- Structural heads use exact source steps; recursive bodies retain only the
original target's contextual typing witness. -/
theorem KUA.typed_step_reverse
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL R y x) fi gi)
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {original bare : Admin} (related : KUA R original bare)
    {originalRest bareRest : List Admin} (rest : KUL R originalRest bareRest)
    {s t : Store H} {f : Frame} {ambient : List Val} {sourceNext : Config H}
    (stores : StoreRel F s t)
    (typed : ContextTyped ⟨t, f, vals ambient ++ [original] ++ originalRest⟩)
    (nonvalue : bare.val? = none)
    (selected : Step P noHost ⟨s, f, vals ambient ++ [bare] ++ bareRest⟩ sourceNext) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      sourceNext ⟨t, f, vals ambient ++ [original] ++ originalRest⟩
      (rank (vals ambient ++ [bare] ++ bareRest)) := by
  cases related with
  | label continuation body =>
    exact kernel_label_step_reverse hF budget labels stores continuation body rest typed.label
      (fun actual => by
        simpa only [Execution.Core.vals_nil', List.nil_append] using
          KUL.typed_step_reverse hF budget labels body (ambient := []) stores
            (by simpa using typed.label) (by simpa using actual)) selected
  | handler body =>
    exact kernel_handler_step_reverse hF budget labels stores body rest typed.handler
      (fun actual => by
        simpa only [Execution.Core.vals_nil', List.nil_append] using
          KUL.typed_step_reverse hF budget labels body (ambient := []) stores
            (by simpa using typed.handler) (by simpa using actual)) selected
  | frame body =>
    exact kernel_frame_step_reverse hF budget labels stores body rest typed.frame
      (fun actual => by
        simpa only [Execution.Core.vals_nil', List.nil_append] using
          KUL.typed_step_reverse hF budget labels body (ambient := []) stores
            (by simpa using typed.frame) (by simpa using actual)) selected
  | plain head => exact KUA.noncontext_step_reverse hF stores (.plain head) rest nonvalue (by simp [Admin.IsCtx]) selected
  | ref r => exact KUA.noncontext_step_reverse hF stores (.ref r) rest nonvalue (by simp [Admin.IsCtx]) selected
  | callRef d => exact KUA.noncontext_step_reverse hF stores (.callRef d) rest nonvalue (by simp [Admin.IsCtx]) selected
  | retCallRef d => exact KUA.noncontext_step_reverse hF stores (.retCallRef d) rest nonvalue (by simp [Admin.IsCtx]) selected
  | trap => exact KUA.noncontext_step_reverse hF stores (.trap) rest nonvalue (by simp [Admin.IsCtx]) selected
termination_by sizeOf original
decreasing_by
  all_goals subst original
  all_goals simp_wf
end

end Silmaril.Wasm.Binaryen.Unwrap
