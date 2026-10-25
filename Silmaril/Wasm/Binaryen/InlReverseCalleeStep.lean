module

public import Silmaril.Wasm.Binaryen.InlReverseCalleeHeads
public import Silmaril.Wasm.Binaryen.InlReverseControl
public import Silmaril.Wasm.Binaryen.InlReverseCalleeContext
public import Silmaril.Wasm.Binaryen.InlReverseFrameModes
public import Silmaril.Wasm.Binaryen.InlReverseIH
public import Silmaril.Wasm.Binaryen.InlReverseCalleeBubble
public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.Execution.Core.Sim.TypedLocalBounds

@[expose] public section

/-! # Complete selected reverse steps in relocated-callee mode

An actual target step determines its original instruction through `AI`, so the
proof retains original local indices and distinguishes relocated returns from
ordinary branches. Labels increase relocation depth, handlers preserve it,
and nested activations recurse into their actual generic or caller relation.
No numerical determinism hypothesis is used.
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

private theorem reverse_callee_flat_context (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {vs args : List Val} {old head : Admin} {oldRest rest : List Admin} {next : Config H}
    (heads : AI p d old head)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (typed : ContextTyped ⟨s, F, vals (vs ++ args) ++ old :: oldRest⟩)
    (suffix : LI p d oldRest rest)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ReverseMatch p P (.i d L) ⟨s, F, vals (vs ++ args) ++ old :: oldRest⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ := by
  have localBound : ∀ x, (old = .plain (.localGet x) ∨ old = .plain (.localSet x)) →
      x.toNat < F.locals.length := by
    intro x access
    rcases access with rfl | rfl
    · exact typed.active_localGet_bound
    · exact typed.active_localSet_bound
  have matched := reverse_callee_head_match parameters heads moduleEq prefixLength locals
    stores nonlabel nonhandler nonframe localBound selected
  simpa [List.append_assoc] using matched.callee_context vs suffix

private theorem reverse_callee_selected_head (parameters : PrmOk p) {k : Nat}
    (ih : ReverseIH p P H k)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {original rest : List Admin} {vs args : List Val} {head : Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext)
    (bound : sizeOf (vals vs ++ (vals args ++ head :: rest)) < k + 1)
    (typed : ContextTyped ⟨s, F, original⟩)
    (related : LI p d original (vals vs ++ (vals args ++ head :: rest)))
    (stores : SR p s t)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ReverseProgress p P (.i d L) ⟨s, F, original⟩
      ⟨t, ⟨L ++ F.locals, p.mi⟩, vals vs ++ (vals args ++ head :: rest)⟩
      ⟨next.store, next.frame, vals vs ++ next.code ++ rest⟩ := by
  have headBound : sizeOf head < k := by
    have smaller := sizeOf_active_head_lt vs args head rest
    omega
  obtain ⟨oldHead, oldRest, oldShape, headRelated, suffix⟩ :=
    LI.vals_cons_reverse (vs := vs ++ args) (by simpa using related)
  subst original
  cases headRelated with
  | label contGood bodyRelated =>
    rcases reverse_callee_label moduleEq prefixLength locals stores contGood bodyRelated selected with
      ⟨bodyNext, rfl, inner, rfl⟩ | ⟨oldNext, actual, runtime, nextStores⟩
    · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_label_body.trans headBound
      have innerTyped := ContextTyped.label (by simpa using typed)
      have matched := ih.callee bodyBound innerTyped
        ⟨moduleEq, prefixLength, locals, rfl, bodyRelated⟩ stores inner
      simpa using (matched.callee_label _ contGood).callee_context vs suffix
    · exact .inl (by simpa [List.append_assoc] using
        (ReverseMatch.of_steps (.single actual.toStep) runtime nextStores).callee_context vs suffix)
  | handler bodyRelated =>
    rcases reverse_callee_handler moduleEq prefixLength locals stores bodyRelated selected with
      ⟨bodyNext, rfl, inner, rfl⟩ | ⟨oldNext, actual, runtime, nextStores⟩
    · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_handler_body.trans headBound
      have innerTyped := ContextTyped.handler (by simpa using typed)
      have matched := ih.callee bodyBound innerTyped
        ⟨moduleEq, prefixLength, locals, rfl, bodyRelated⟩ stores inner
      simpa using (matched.callee_handler _ _).callee_context vs suffix
    · exact .inl (by simpa [List.append_assoc] using
        (ReverseMatch.of_steps (.single actual.toStep) runtime nextStores).callee_context vs suffix)
  | frame frameRelated =>
    rcases reverse_callee_frame moduleEq prefixLength locals stores frameRelated selected with
      ⟨bodyNext, rfl, frames, inner, rfl⟩ | matched
    · have bodyBound : sizeOf _ < k := Exec.Drv.sizeOf_frame_body.trans headBound
      have innerTyped := ContextTyped.frame (by simpa using typed)
      rcases frames.runtime_modes with generic | caller
      · have matched := ih.generic bodyBound innerTyped generic stores inner
        simpa using (matched.callee_frame_gen _ F moduleEq prefixLength locals).callee_context vs suffix
      · have matched := ih.caller bodyBound innerTyped caller stores inner
        simpa using (matched.callee_frame_caller _ F moduleEq prefixLength locals).callee_context vs suffix
    · exact .inl (by simpa [List.append_assoc] using matched.callee_context vs suffix)
  | plain good =>
    exact .inl (reverse_callee_flat_context parameters (.plain good)
      moduleEq prefixLength locals stores typed suffix
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) selected)
  | callRef dt =>
    exact .inl (reverse_callee_flat_context parameters (.callRef dt)
      moduleEq prefixLength locals stores typed suffix
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) selected)
  | ref value => exact absurd selected.good.val_none (by simp)
  | trap => exact (selected.good.ne_trap rfl).elim

/-- Replay every actual selected target step in relocated-callee mode. Only
smaller active target bodies are delegated to the joint induction hypothesis. -/
theorem reverse_callee_step (parameters : PrmOk p) {k : Nat}
    (ih : ReverseIH p P H k) {d : Nat} {L : List (Option Val)}
    {original target next : Config H}
    (bound : sizeOf target.code < k + 1) (typed : ContextTyped original)
    (runtime : MR p (.i d L) original target) (stores : SR p original.store target.store)
    (selected : Step P Det.noHost target next) :
    ReverseProgress p P (.i d L) original target next := by
  obtain ⟨s, F, original⟩ := original
  obtain ⟨t, targetFrame, target⟩ := target
  obtain ⟨moduleEq, prefixLength, locals, rfl, related⟩ := runtime
  rcases Det.Step.decomp selected with
    ⟨vs, args, head, rest, headNext, shape, headStep, rfl⟩ |
      ⟨pp, q, kernel, discarded, rest, shape, bubble, nonempty, rfl⟩
  · simp only at shape
    rw [shape] at related bound
    simpa [shape] using reverse_callee_selected_head parameters ih
      moduleEq prefixLength locals bound typed related stores headStep
  · simp only at shape
    rw [shape] at related
    obtain ⟨oldNext, actual, nextRuntime, nextStores⟩ := reverse_callee_bubble
      moduleEq prefixLength locals stores bubble nonempty related
    exact .inl (ReverseMatch.of_steps (.single actual) nextRuntime nextStores)

end Silmaril.Wasm.Binaryen.InlR
