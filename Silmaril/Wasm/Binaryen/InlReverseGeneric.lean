module

public import Silmaril.Wasm.Binaryen.InlReverseProgress
public import Silmaril.Wasm.Binaryen.InlReverseGenericControl
public import Silmaril.Wasm.Binaryen.InlReverseFrame
public import Silmaril.Wasm.SingleThreaded.Exec.Driver

@[expose] public section

/-! # The complete chosen reverse step in generic mode

The target's actual head decomposition reconstructs the original value prefix,
active instruction and related suffix. Recursive bodies retain their original
typing inside the full active context. Every numerical choice is the one made
by the selected target step; no outcome uniqueness assumption is used.
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

private theorem reverse_generic_head (parameters : PrmOk p) {k : Nat}
    (ih : ReverseIH p P H k)
    {s t : Store H} {frame : Frame} {original rest : List Admin}
    {vs args : List Val} {head : Admin} {next : Config H}
    (bound : sizeOf (vals vs ++ (vals args ++ head :: rest)) < k + 1)
    (typed : ContextTyped ⟨s, frame, original⟩)
    (related : LN p original (vals vs ++ (vals args ++ head :: rest)))
    (stores : SR p s t) (selected : Det.Head P t frame args head next) :
    ReverseProgress p P .gen ⟨s, frame, original⟩
      ⟨t, frame, vals vs ++ (vals args ++ head :: rest)⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ := by
  have headBound : sizeOf head < k := by
    have smaller := sizeOf_active_head_lt vs args head rest
    omega
  obtain ⟨oldHead, oldRest, oldShape, headRelated, suffixRelated⟩ :=
    LN.vals_cons_inv_right (vs := vs ++ args) (by simpa using related)
  subst original
  cases headRelated with
  | label bodyRelated =>
    rcases reverse_generic_label bodyRelated stores selected with
      ⟨bodyNext, rfl, inner, rfl⟩ | ⟨oldNext, oldHead, runtime, nextStores⟩
    · have bodyBound : sizeOf _ < k :=
        (Exec.Drv.sizeOf_label_body).trans headBound
      have innerTyped := ContextTyped.label (by simpa using typed)
      have matched := ih.generic (target := ⟨t, frame, _⟩) (next := bodyNext)
        bodyBound innerTyped ⟨rfl, bodyRelated⟩ stores inner
      simpa using (matched.label _ _).context vs suffixRelated
    · have matched := ReverseMatch.of_steps (.single oldHead.toStep) runtime nextStores
      exact .inl (by simpa [List.append_assoc] using matched.context vs suffixRelated)
  | handler bodyRelated =>
    rcases reverse_generic_handler bodyRelated stores selected with
      ⟨bodyNext, rfl, inner, rfl⟩ | ⟨oldNext, oldHead, runtime, nextStores⟩
    · have bodyBound : sizeOf _ < k :=
        (Exec.Drv.sizeOf_handler_body).trans headBound
      have innerTyped := ContextTyped.handler (by simpa using typed)
      have matched := ih.generic (target := ⟨t, frame, _⟩) (next := bodyNext)
        bodyBound innerTyped ⟨rfl, bodyRelated⟩ stores inner
      simpa using (matched.handler _ _).context vs suffixRelated
    · have matched := ReverseMatch.of_steps (.single oldHead.toStep) runtime nextStores
      exact .inl (by simpa [List.append_assoc] using matched.context vs suffixRelated)
  | frame frameRelated =>
    rcases reverse_generic_frame stores frameRelated selected with
      ⟨bodyNext, rfl, frames, inner, rfl⟩ | matched
    · have bodyBound : sizeOf _ < k :=
        (Exec.Drv.sizeOf_frame_body).trans headBound
      have innerTyped := ContextTyped.frame (by simpa using typed)
      rcases frames.runtime_modes with generic | caller
      · have matched := ih.generic bodyBound innerTyped generic stores inner
        simpa using (matched.frame_gen _ frame).context vs suffixRelated
      · have matched := ih.caller bodyBound innerTyped caller stores inner
        simpa using (matched.frame_caller _ frame).context vs suffixRelated
    · exact .inl (by simpa [List.append_assoc] using matched.context vs suffixRelated)
  | _ =>
    obtain ⟨oldNext, step, runtime, nextStores⟩ :=
      reverse_generic_flat_context parameters stores related
        (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
        (fun _ _ _ h => by cases h) selected
    exact .inl (ReverseMatch.of_steps (.single step) runtime nextStores)

/-- Match any selected target step of generic code, recursively through every
runtime label, handler and activation. Smaller target-body obligations are
supplied together for generic and changed-caller modes. -/
theorem reverse_generic_step (parameters : PrmOk p) {k : Nat}
    (ih : ReverseIH p P H k) {original target next : Config H}
    (bound : sizeOf target.code < k + 1) (typed : ContextTyped original)
    (runtime : MR p .gen original target) (stores : SR p original.store target.store)
    (selected : Step P Det.noHost target next) :
    ReverseProgress p P .gen original target next := by
  obtain ⟨s, frame, original⟩ := original
  obtain ⟨t, targetFrame, target⟩ := target
  obtain ⟨rfl, related⟩ := runtime
  rcases Det.Step.decomp selected with
    ⟨vs, args, head, rest, headNext, shape, headStep, rfl⟩ |
      ⟨pp, q, kernel, discarded, rest, shape, bubble, nonempty, rfl⟩
  · simp only at shape
    rw [shape] at related bound
    simpa [shape] using reverse_generic_head parameters ih bound typed related stores headStep
  · simp only at shape
    rw [shape] at related
    obtain ⟨oldNext, step, nextRuntime, nextStores⟩ :=
      reverse_generic_bubble bubble nonempty related stores
    exact .inl (ReverseMatch.of_steps (.single step) nextRuntime nextStores)

end Silmaril.Wasm.Binaryen.InlR
