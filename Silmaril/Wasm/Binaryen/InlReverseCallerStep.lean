module

public import Silmaril.Wasm.Binaryen.InlReverseCallerBubble
public import Silmaril.Wasm.Binaryen.InlReverseCallerHeads
public import Silmaril.Wasm.Binaryen.InlReverseSiteAdvanced
public import Silmaril.Wasm.Binaryen.InlReverseCalleeContext
public import Silmaril.Wasm.Binaryen.InlReverseFrameModes
public import Silmaril.Wasm.Binaryen.InlReverseIH
public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.Execution.Core.Sim.TypedLocalBounds

@[expose] public section

/-! # Complete selected reverse steps in changed-caller mode

The actual target head determines the source instruction and recursive body.
Active inline sites retain the source activation and its depth-zero relocation
relation; ordinary caller contexts retain independently related continuations.
Dead trap and exception suffixes use either actual source progress or a strict
decrease in the target's administrative rank.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

private theorem sizeOf_suffix_le (pre suffix : List Admin) :
    sizeOf suffix ≤ sizeOf (pre ++ suffix) := by
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    simp only [List.cons_append, List.cons.sizeOf_spec]
    omega

private theorem sizeOf_active_head_lt (vs args : List Val) (head : Admin)
    (rest : List Admin) :
    sizeOf head < sizeOf (vals vs ++ (vals args ++ head :: rest)) := by
  have inside : sizeOf head < sizeOf (head :: rest) := by
    simp only [List.cons.sizeOf_spec]
    omega
  exact inside.trans_le ((sizeOf_suffix_le (vals args) _).trans
    (sizeOf_suffix_le (vals vs) _))

private theorem reverse_caller_flat_context (parameters : PrmOk p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    {vs args : List Val} {head : Admin} {oldRest rest : List Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (typed : ContextTyped ⟨s, fo, vals (vs ++ args) ++ head :: oldRest⟩)
    (suffix : LGq p oldRest rest)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (nonstruct : ¬ StructE head)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ReverseMatch p P .g ⟨s, fo, vals (vs ++ args) ++ head :: oldRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ := by
  have localBound : ∀ x, (head = .plain (.localGet x) ∨ head = .plain (.localSet x)) →
      x.toNat < fo.locals.length := by
    intro x access
    rcases access with rfl | rfl
    · exact typed.active_localGet_bound
    · exact typed.active_localSet_bound
  obtain ⟨oldNext, actual, runtime, related⟩ := reverse_caller_flat_head parameters
    moduleEq locals extra stores nonlabel nonhandler nonframe nonstruct localBound selected
  simpa [List.append_assoc] using
    (ReverseMatch.of_steps (.single actual.toStep) runtime related).caller_context vs suffix

private theorem reverse_caller_head (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af) {k : Nat}
    (ih : ReverseIH p P H k)
    {s t : Store H} {fo : Frame} {E : List (Option Val)} {original rest : List Admin}
    {vs args : List Val} {head : Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext)
    (bound : sizeOf (vals vs ++ (vals args ++ head :: rest)) < k + 1)
    (typed : ContextTyped ⟨s, fo, original⟩)
    (related : LG p E original (vals vs ++ (vals args ++ head :: rest)))
    (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ReverseProgress p P .g ⟨s, fo, original⟩
      ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals vs ++ (vals args ++ head :: rest)⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ := by
  have headBound : sizeOf head < k := by
    have smaller := sizeOf_active_head_lt vs args head rest
    omega
  rcases LG.vals_cons_inv_right (vs := vs ++ args) selected.good.val_none
      (by simpa using related) with ordinary | pending | trapped | thrown
  · obtain ⟨oldHead, oldRest, oldShape, headRelated, suffix⟩ := ordinary
    subst original
    cases headRelated with
    | plain instructionRelated =>
      rename_i old instruction
      by_cases structured : StructE (.plain instruction)
      · have matched := reverse_caller_structured_head parameters initialization functionIndex
          instructionRelated moduleEq locals extra stores structured selected
        exact .inl (by simpa [List.append_assoc] using matched.caller_context vs suffix)
      · obtain rfl := instructionRelated.eq_of_nonstruct_right structured
        exact .inl (reverse_caller_flat_context parameters moduleEq locals extra stores
          typed suffix (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h) structured selected)
    | label continuations bodyRelated =>
      rcases reverse_caller_label moduleEq locals extra stores continuations bodyRelated selected with
        ⟨bodyNext, rfl, inner, rfl⟩ | matched
      · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_label_body.trans headBound
        have innerTyped := ContextTyped.label (by simpa using typed)
        have matched := ih.caller bodyBound innerTyped
          ⟨moduleEq, locals, E, extra, rfl, bodyRelated⟩ stores inner
        simpa using (matched.caller_label _ continuations).caller_context vs suffix
      · exact .inl (by simpa [List.append_assoc] using matched.caller_context vs suffix)
    | handler bodyRelated =>
      rcases reverse_caller_handler moduleEq locals extra stores bodyRelated selected with
        ⟨bodyNext, rfl, inner, rfl⟩ | matched
      · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_handler_body.trans headBound
        have innerTyped := ContextTyped.handler (by simpa using typed)
        have matched := ih.caller bodyBound innerTyped
          ⟨moduleEq, locals, E, extra, rfl, bodyRelated⟩ stores inner
        simpa using (matched.caller_handler _ _).caller_context vs suffix
      · exact .inl (by simpa [List.append_assoc] using matched.caller_context vs suffix)
    | frame frameRelated =>
      rcases reverse_caller_frame moduleEq locals extra stores frameRelated selected with
        ⟨bodyNext, rfl, frames, inner, rfl⟩ | matched
      · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_frame_body.trans headBound
        have innerTyped := ContextTyped.frame (by simpa using typed)
        rcases frames.runtime_modes with generic | caller
        · have matched := ih.generic bodyBound innerTyped generic stores inner
          simpa using (matched.caller_frame_gen _ fo moduleEq locals extra).caller_context vs suffix
        · have matched := ih.caller bodyBound innerTyped caller stores inner
          simpa using (matched.caller_frame_caller _ fo moduleEq locals extra).caller_context vs suffix
      · exact .inl (by simpa [List.append_assoc] using matched.caller_context vs suffix)
    | site calleeModule calleeLocals site =>
      subst E
      obtain rfl := reverse_site_label_args selected
      obtain ⟨C, results, wf, noLabels, _, arity, bodyTyped, _⟩ := typed.active_frame_typing
      rcases reverse_site_selected_head moduleEq rfl locals extra stores wf noLabels arity
          bodyTyped site selected with contextual | ⟨oldNext, actual, runtime, nextStores⟩
      · obtain ⟨oldBody, bodyNext, rfl, bodyRelated, _, inner, rfl⟩ := contextual
        have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_label_body.trans headBound
        have frameTyped := ContextTyped.frame (vs := vs) (rest := oldRest) (by simpa using typed)
        have innerTyped := ContextTyped.label (vs := []) (rest := []) (by simpa using frameTyped)
        have matched := ih.callee (d := 0) (L := fo.locals) bodyBound innerTyped
          ⟨calleeModule, locals, extra, rfl, bodyRelated⟩ stores inner
        simpa using (matched.inline_site moduleEq _).caller_context vs suffix
      · exact .inl (by simpa [List.append_assoc] using
          (ReverseMatch.of_steps actual runtime nextStores).caller_context vs suffix)
    | ref value =>
      have impossible := selected.good.val_none
      simp [Admin.val?] at impossible
    | callRef dt | retCallRef dt =>
      exact .inl (reverse_caller_flat_context parameters moduleEq locals extra stores
        typed suffix (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (by simp [StructE]) selected)
    | trap => exact (selected.good.ne_trap rfl).elim
  · obtain ⟨rfl, oldRest, oldShape, suffix⟩ := pending
    subst original
    have matched := reverse_caller_site_pending parameters initialization
      moduleEq locals extra stores selected
    exact .inl (by simpa [List.append_assoc, Val.toAdmin] using matched.caller_context vs suffix)
  · obtain ⟨rfl, _⟩ := trapped
    exact (selected.good.ne_trap rfl).elim
  · obtain ⟨rfl, oldRest, oldShape⟩ := thrown
    subst original
    obtain rfl := selected.good.throwRef rfl
    have actual : Step P Det.noHost
        ⟨s, fo, vals [.ref .null] ++ [.plain .throwRef]⟩ ⟨s, fo, [.trap]⟩ :=
      Det.Head.toStep .throwRefNull
    cases selected with
    | throwRefNull =>
      have steps : Relation.TransGen (Step P Det.noHost)
          ⟨s, fo, vals (vs ++ [.ref .null]) ++ .plain .throwRef :: oldRest⟩
          ⟨s, fo, vals vs ++ .trap :: oldRest⟩ := by
        simpa [List.append_assoc] using tg_instrs (.single actual) vs oldRest
      have runtime : MR p .g ⟨s, fo, vals vs ++ .trap :: oldRest⟩
          ⟨t, ⟨fo.locals ++ E, p.mi⟩, vals vs ++ [.trap] ++ rest⟩ :=
        ⟨moduleEq, locals, E, extra, rfl, by
          simpa using LG.vals_append vs (.trapT : LG p E (.trap :: oldRest) (.trap :: rest))⟩
      exact .inl (ReverseMatch.of_steps steps runtime stores)
    | parametric h => fam_dismiss
    | numeric h => fam_dismiss
    | vector h => fam_dismiss
    | «variable» h => fam_dismiss
    | table h => fam_dismiss
    | memory h => fam_dismiss
    | reference h => fam_dismiss
    | aggregate h => fam_dismiss
    | callRefNull call => exact absurd call (by simp [Admin.IsCallRef])
    | callRefFunc _ call => exact absurd call (by simp [Admin.IsCallRef])

/-- Replay every actual selected target step in caller mode. Recursive
obligations are only for smaller active target bodies, across all runtime modes. -/
theorem reverse_caller_step (parameters : PrmOk p) (initialization : PrmC p)
    (functionIndex : p.mi.funcs[p.fx.toNat]? = some p.af) {k : Nat}
    (ih : ReverseIH p P H k) {original target next : Config H}
    (bound : sizeOf target.code < k + 1) (typed : ContextTyped original)
    (runtime : MR p .g original target) (stores : SR p original.store target.store)
    (selected : Step P Det.noHost target next) :
    ReverseProgress p P .g original target next := by
  obtain ⟨s, fo, original⟩ := original
  obtain ⟨t, targetFrame, target⟩ := target
  obtain ⟨moduleEq, locals, E, extra, rfl, related⟩ := runtime
  rcases Det.Step.decomp selected with
    ⟨vs, args, head, rest, headNext, shape, headStep, rfl⟩ |
      ⟨pp, q, kernel, discarded, rest, shape, bubble, nonempty, rfl⟩
  · simp only at shape
    rw [shape] at related bound
    simpa [shape] using reverse_caller_head parameters initialization functionIndex ih
      moduleEq locals extra bound typed related stores headStep
  · simp only at shape
    rw [shape] at related
    simpa [shape] using reverse_caller_bubble moduleEq locals extra stores bubble nonempty related

end Silmaril.Wasm.Binaryen.InlR
