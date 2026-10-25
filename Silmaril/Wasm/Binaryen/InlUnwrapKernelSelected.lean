module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelSite
public import Silmaril.Wasm.Binaryen.InlUnwrapKernelStatic
public import Silmaril.Wasm.Binaryen.InlUnwrapKernelValuesPrefix

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} [LawfulCodeRank rank]

/-- Reconstruct the exact computational reduction selected by decomposition. -/
theorem selected_head_step {s : Store H} {f : Frame} {code : List Admin} {next : Config H}
    (selected : HeadDec P s f code next) : Step P noHost ⟨s, f, code⟩ next := by
  obtain ⟨ambient, args, e, tail, result, rfl, head, rfl⟩ := selected
  simpa only [List.append_assoc, List.singleton_append] using
    Step.append_right (Step.vals_left head.toStep ambient) tail

/-- Identify an actual selected head at a known first non-value. This retains
the complete chosen result and its exact operand split. -/
theorem selected_head_at_first {s : Store H} {f : Frame} {code : List Admin} {next : Config H}
    {values : List Val} {e : Admin} {tail : List Admin}
    (shape : code = vals values ++ e :: tail) (he : e.val? = none)
    (selected : HeadDec P s f code next) :
    ∃ ambient args result, values = ambient ++ args ∧ Head P s f args e result ∧
      next = ⟨result.store, result.frame, vals ambient ++ result.code ++ tail⟩ := by
  obtain ⟨ambient, args, other, rest, result, selectedShape, head, after⟩ := selected
  have aligned : vals values ++ e :: tail = vals (ambient ++ args) ++ other :: rest := by
    simpa only [vals_append, List.append_assoc] using shape.symm.trans selectedShape
  obtain ⟨operands, rfl, rfl⟩ := Sim.vals_append_cons_inj he head.good.val_none aligned
  exact ⟨ambient, args, result, operands, head, after⟩

/-- Complete actual-head matching for a folded runtime label. Its body may
contain arbitrary recursive kernel cuts and may already be values. -/
theorem folded_label_head_reverse
    {F : FuncInst H → FuncInst H → Prop}
    (budget : ∃ S, ∀ i ∈ R, InstrB budU S i) (labels : instrsLabels R = [])
    {s t : Store H} {f : Frame} {n : Nat}
    {original bare common originalRest bareRest : List Admin}
    {ambient outer args : List Val} {next : Config H}
    (stores : StoreRel F s t) (body : KUL R original bare)
    (safe : NoEsc (original ++ common)) (rest : KUL R originalRest bareRest)
    (typed : ContextTyped
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩)
    (inside : ∀ {sourceNext : Config H}, Step P noHost ⟨s, f, bare⟩ sourceNext →
      RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
        sourceNext ⟨t, f, original⟩ (rank bare))
    (head : Head P s f args (.label n [] bare) next)
    (split : ambient = outer ++ args) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨next.store, next.frame, vals outer ++ next.code ++ (common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [.label n [] (original ++ common)] ++ originalRest⟩
      (rank (vals ambient ++ [.label n [] bare] ++ (common ++ bareRest))) := by
  have typedBody : ContextTyped ⟨t, f, original⟩ :=
    ContextTyped.suffix (ContextTyped.label typed)
  cases head with
  | ctxtLabel selected =>
    simp only [List.append_nil] at split
    subst ambient
    exact folded_body_step_match safe rest selected (inside selected)
  | labelVals values =>
    simp only [List.append_nil] at split
    subst ambient
    subst bare
    exact folded_values_match stores body safe rest typed
  | trapLabel =>
    simp only [List.append_nil] at split
    subst ambient
    exact folded_kernel_match stores body typed (Or.inl rfl)
  | throwRefLabel =>
    simp only [List.append_nil] at split
    subst ambient
    exact folded_kernel_match stores body typed (Or.inr ⟨_, rfl⟩)
  | brLabelZero shape _ _ =>
    rename_i leftValues rightValues label suffix zero arity
    exact (KUL.no_blocked_of_guard budget labels body safe typedBody
      (values := leftValues ++ rightValues) (e := .plain (.br label)) (rest := suffix)
      (by simpa only [vals_append, List.append_assoc, List.singleton_append] using shape)
      rfl (Or.inl ⟨_, rfl⟩)).elim
  | brLabelSucc shape _ =>
    exact (KUL.no_blocked_of_guard budget labels body safe typedBody
      (by simpa only [List.append_assoc, List.singleton_append] using shape)
      rfl (Or.inl ⟨_, rfl⟩)).elim
  | returnLabel shape =>
    exact (KUL.no_blocked_of_guard budget labels body safe typedBody
      (by simpa only [List.append_assoc, List.singleton_append] using shape)
      rfl (Or.inr (Or.inl rfl))).elim
  | returnCallRefLabel shape call =>
    exact (KUL.no_blocked_of_guard budget labels body safe typedBody
      (by simpa only [List.append_assoc, List.singleton_append] using shape)
      (Admin.val?_of_isReturnCallRef call) (Or.inr (Or.inr call))).elim
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

end Silmaril.Wasm.Binaryen.Unwrap
